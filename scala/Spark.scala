import scala.language.implicitConversions

object Prelude {

  type Partition[A] = List[A]
  type RDD[A] = List[Partition[A]]
  type PairRDD[A, B] = RDD[Pair[A, B]]

  class Pair[A, B] (val key: A, val value: B)

  implicit def TupleToPair[A, B] (t: (A, B)): Pair[A, B] = new Pair(t._1, t._2)

  /** ************************
    * Deterministic operations
    * ************************/

  def map[A, B] (pa: Partition[A])(fn: A => B): Partition[B] =
    pa match {
      case Nil     => Nil
      case x :: xs => fn(x) :: map(xs)(fn)
    }

  def filter[A] (pa: Partition[A])(fn: A => Boolean): Partition[A] =
    pa match {
      case Nil     => Nil
      case x :: xs => if (fn(x)) x :: filter(xs)(fn) else filter(xs)(fn)
    }

  def foldl[A, B] (pa: Partition[A])(z: B)(fn: (B, A) => B): B =
    pa match {
      case Nil     => z
      case x :: xs => foldl(xs)(fn(z, x))(fn)
    }

  def reducel[A] (pa: Partition[A])(fn: (A, A) => A): A =
    pa match {
      case x :: xs => foldl(xs)(x)(fn)
      case Nil     => throw new Error("empty list")
    }

  def concat[A] (rdd: RDD[A]): Partition[A] =
    rdd match {
      case Nil     => Nil
      case x :: xs => x ++ concat(xs)
    }

  def concatMap[A, B] (pa: Partition[A])(fn: A => Partition[B]): Partition[B] =
    concat(map(pa)(fn))

  def hasValue[A, B] (pa: Partition[Pair[A, B]])(default: B)(key: A) =
    foldl(pa)(default) {
      (value, pair) => if (pair.key == key) pair.value else value
    }

  def hasKey[A, B] (pa: Partition[Pair[A, B]])(key: A): Boolean =
    foldl(pa)(false) {
      (found, pair) => if (pair.key == key) true else found
    }

  def addTo[A, B] (pa: Partition[Pair[A, B]])(pair: Pair[A, B]): Partition[Pair[A, B]] =
    foldl(pa)(List(pair)) {
      (p1, p2) => if (pair.key == p2.key) p1 else p2 :: p1
    }

  def lookup[A, B] (pa: Partition[Pair[A, B]])(key: A): Option[B] =
    foldl(pa)(None: Option[B]) {
      (p1, p2) => if (p2.key == key) Some(p2.value) else p1
    }

  /** ****************************
    * Non-deterministic operations
    * ****************************/

  /* Nondeterministic map */
  def mapX[A, B] (pa: Partition[A])(fn: A => B): Partition[B] = map(pa)(fn)

  /* Nondeterministic concatMap */
  def concatMapX[A, B] (pa: Partition[A])(fn: A => Partition[B]): Partition[B] = concat(mapX(pa)(fn))

  /* Nondeterministic re-partitioning */
  def shufflePartitionX[A] (pa: Partition[A]): RDD[A] = List(pa)

  def aggregate[A, B] (rdd: RDD[A])(z: B)(seq: (B, A) => B)(comb: (B, B) => B): B =
    foldl(mapX(rdd)(foldl(_)(z)(seq)))(z)(comb)

  def reduce[A] (rdd: RDD[A])(comb: (A, A) => A): A =
    reducel(mapX(rdd)(reducel(_)(comb)))(comb)

  def aggregateByKey[A, B, C] (rdd: PairRDD[A, B])(z: C)(mergeComb: (C, B) => C, mergeValue: (C, C) => C): PairRDD[A, C] = {
    def seq[D] (f: (C, D) => C)(pa: Partition[Pair[A, C]], p: Pair[A, D]) =
      addTo(pa)(p.key, f(hasValue(pa)(z)(p.key), p.value))
    val zero: Partition[Pair[A, C]] = Nil
    val preAggrs = concatMapX(rdd)(foldl(_)(zero)(seq(mergeComb)))
    shufflePartitionX(foldl(preAggrs)(zero)(seq(mergeValue)))
  }

  def aggregateWithKey[A, B, C] (rdd: PairRDD[A, B])(key: A)(z: C)(mergeComb: (C, B) => C, mergeValue: (C, C) => C): C = {
    val preAggrs = filter(map(rdd) {
      pa => map(filter(pa)(_.key == key))(_.value)
    })(_ != Nil)
    aggregate(preAggrs)(z)(mergeComb)(mergeValue)
  }

  def reduceByKey[A, B] (rdd: PairRDD[A, B])(comb: (B, B) => B): PairRDD[A, B] = {
    def merge (pa: Partition[Pair[A, B]], p: Pair[A, B]) =
      lookup(pa)(p.key) match {
        case None    => addTo(pa)(p.key, p.value)
        case Some(v) => addTo(pa)(p.key, comb(v, p.value))
      }
    val z: Partition[Pair[A, B]] = Nil
    shufflePartitionX(foldl(concatMapX(rdd)(foldl(_)(z)(merge)))(z)(merge))
  }

  def reduceWithKey[A, B] (rdd: PairRDD[A, B])(key: A)(comb: (B, B) => B): B = {
    val preAggrs = map(rdd) {
      pa => map(filter(pa)(_.key == key))(_.value)
    }
    reduce(filter(preAggrs)(_ != Nil))(comb)
  }
}

object GraphX {

  import Prelude._

  case class Edge[B] (srcId: VertexId,
                      dstId: VertexId,
                      attr: B) extends Pair((srcId, dstId), attr)

  case class Vertex[A] (id: VertexId,
                        attr: A) extends Pair(id, attr)

  case class EdgeTriplet[A, B] (srcId: VertexId, srcAttr: A,
                                dstId: VertexId, dstAttr: A,
                                attr: B) extends Pair((srcId, dstId), attr)

  type VertexId = Int
  type VertexRDD[A] = RDD[Vertex[A]]
  type EdgeRDD[B] = RDD[Edge[B]]

  case class GraphRDD[A, B] (vertexRDD: VertexRDD[A], edgeRDD: EdgeRDD[B])

  implicit def PairRDDToVertexRDD[A] (rdd: PairRDD[VertexId, A]): VertexRDD[A] =
    map(rdd)(map(_)(p => Vertex(p.key, p.value)))

  def aggregateMessages[A, B, C] (graph: GraphRDD[A, B])
                                 (sendMsg: EdgeTriplet[A, B] => List[Vertex[C]])
                                 (mergeMsg: (C, C) => C): VertexRDD[C] =
    aggregateMessagesWithActiveSet(graph)(sendMsg)(mergeMsg)(concat(graph.vertexRDD))

  def aggregateMessagesWithActiveSet[A, B, C] (graph: GraphRDD[A, B])
                                              (sendMsg: EdgeTriplet[A, B] => List[Vertex[C]])
                                              (mergeMsg: (C, C) => C)
                                              (activeSet: List[Vertex[A]]): VertexRDD[C] = {
    val edgeRDD = filter(map(graph.edgeRDD)(filter(_) {
      e => hasKey(activeSet)(e.srcId) || hasKey(activeSet)(e.dstId)
    }))(_ != Nil)
    val vAttrs = concat(graph.vertexRDD)
    def f (edge: Edge[B]) = {
      val Some(srcAttr) = lookup(vAttrs)(edge.srcId)
      val Some(dstAttr) = lookup(vAttrs)(edge.dstId)
      sendMsg(EdgeTriplet(edge.srcId, srcAttr, edge.dstId, dstAttr, edge.attr))
    }
    reduceByKey(mapX(edgeRDD)(concatMap(_)(f)))(mergeMsg)
  }

  def mapVertices[A, C] (vertices: VertexRDD[A])(fn: Vertex[A] => C): VertexRDD[C] =
    mapX(vertices)(map(_)(v => Vertex(v.id, fn(v))))

  def Pregel[A, B, C] (graph: GraphRDD[A, B])
                      (initMsg: C)
                      (vprog: (Vertex[A], C) => A)
                      (sendMsg: EdgeTriplet[A, B] => List[Vertex[C]])
                      (mergeMsg: (C, C) => C): GraphRDD[A, B] = {

    val initGraph = GraphRDD(mapVertices(graph.vertexRDD)(vprog(_, initMsg)), graph.edgeRDD)
    val initMsgs = concat(aggregateMessages(initGraph)(sendMsg)(mergeMsg))

    def loop (graph: GraphRDD[A, B], msgs: List[Vertex[C]]): GraphRDD[A, B] =
      if (msgs == Nil)
        graph
      else {
        val newGraph = GraphRDD(
          mapVertices(graph.vertexRDD) {
            v => lookup(msgs)(v.id) match {
              case None       => v.attr
              case Some(attr) => vprog(v, attr)
            }
          },
          graph.edgeRDD
        )
        val activeSet = filter(concat(graph.vertexRDD))(v => hasKey(msgs)(v.id))
        val newMsgs = concat(aggregateMessagesWithActiveSet(newGraph)(sendMsg)(mergeMsg)(activeSet))
        loop(newGraph, newMsgs)
      }
    loop(initGraph, initMsgs)
  }
}
