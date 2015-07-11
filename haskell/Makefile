TARGET=	AUC Graph TriangleCount ConnectedComponent RandomizedGraphColoring

all: $(TARGET)

AUC:	Spark.hs AUC.hs
	ghc -o AUC --make AUC

Graph:	Spark.hs Graph.hs
	ghc -o Graph --make Graph

TriangleCount:	Spark.hs TriangleCount.hs
	ghc -o TriangleCount --make TriangleCount

ConnectedComponent: Spark.hs ConnectedComponent.hs
	ghc -o ConnectedComponent --make ConnectedComponent

RandomizedGraphColoring: Spark.hs RandomizedGraphColoring.hs
	ghc -o RandomizedGraphColoring --make RandomizedGraphColoring

clean:
	rm -f *.o *.hi $(TARGET)

.o.hs:
	ghc -c $<

