
\documentclass{article}

\usepackage{amsmath}
\usepackage{amsthm}

%include lhs2TeX.fmt
%include forall.fmt
%include polycode.fmt

%include Formatting.fmt

%let showproofs = True

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}

\begin{document}

\paragraph{Simple aggregation} Recall the definitions:

> type Partition a = [a]
> type RDD a = [Partition a]

> aggregate :: b -> (b -> a -> b) -> (b -> b -> b) -> RDD a -> b
> aggregate z otimes oplus = foldl oplus z . map (foldl otimes z)

\paragraph{Aggregation for pair RDDs}
Extending aggregation to pair RDDs:

> type PairRDD a b = RDD (a,b)

> key :: (a,b) -> a
> key = fst
> value :: (a,b) -> b
> value = snd


The functional call |hasValye k v ps| locates the rightmost occurrence
of |(k,u)| in |ps|, if any, and returns |u|. Otherwise it returns the
default value |v|.

> hasValue :: Eq a => a -> b -> [(a,b)] -> b
> hasValue k v ps = last' v (map value (filter ((== k) . key) ps))

where |last' v = last . (v:)| (thus |last' v [] = v|). The definition
above is equivalent to |foldl (\r p -> if k == key p then value p
else r) v|. Also, let |keyEq k = (==k) . key|, since we use it often

%if False

> last' z = last . (z:)
> keyEq k = (==k) . key
> app = ($)

%endif


The function |addTo| updates a key-value list by a given key-value pair.

> addTo :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
> addTo k v ps = (k,v) : filter (not . (== k) . key) ps

Given |odot :: c -> b -> c|, |lodot :: [(a, c)] -> (a, b) -> [(a, c)]| is
|odot| lifted to list of key-value pairs:

< liftK :: Eq a => (c -> b -> c) -> c -> [(a, c)] -> (a, b) -> [(a, c)]
< r `lodot` (k,v) = addTo k (hasValue k z r `odot` v) r

%if False

> liftK :: Eq a => (c -> b -> c) -> c -> [(a, c)] -> (a, b) -> [(a, c)]
> liftK odot z r (k,v) = addTo k (hasValue k z r `odot` v) r

%endif

It is helpful to give |lodot| an inductive characterization:
\begin{spec}
[]               `lodot` (k,v)  = [(k,z `odot` v)]
(xs ++ [(j,u)])  `lodot` (k,v)  | k == j     = xs ++ [(k,u `odot` v)]
                                | otherwise  = (xs `lodot` (k,v)) ++ [(j,u)]
\end{spec}

The function |repartition| is unspecified. The following dummy definition
is merely there to allow the code to type check.

> repartition :: [(a,b)] -> PairRDD a b
> repartition xs = [xs]

Finally, |aggregateByKey| may be defined by:

> aggregateByKey ::  Eq a => c -> (c -> b -> c) -> (c -> c -> c) ->
>                    PairRDD a b -> PairRDD a c
> aggregateByKey z otimes oplus =
>   repartition . foldl loplus [] . concat . map (foldl lotimes [])

%if False

>  where loplus = liftK oplus z
>        lotimes = liftK otimes z

%endif



\paragraph{Aggregation with a given key}
The function |aggregateWithKey|

> aggregateWithKey :: Eq a =>
>   a -> c -> (c -> b -> c) -> (c -> c -> c) -> PairRDD a b -> c
> aggregateWithKey k z otimes oplus =
>   aggregate z otimes oplus .
>     filter (not . null) .
>       map (map value . filter (keyEq k))

> lookUp :: Eq a => a -> b -> PairRDD a b -> b
> lookUp k z = last' z . concat . map (map value . filter ((== k) . key))

> lookUpL :: Eq a => a -> b -> [(a,b)] -> b
> lookUpL k z = last' z . map value . filter ((== k) . key)

\begin{lemma}
\label{lemma:filter-lift} For all |j|, |k|, |xs|, |v|, |z|, and |odot|, we have:
\begin{enumerate}
  \item  |filter (keyEq k) (xs `lodot` (k,v)) =
  filter (keyEq k) xs `lodot` (k,v)|.
  \item |filter (keyEq k) (xs `lodot` (j,v)) =
  filter (keyEq k) xs|, if |k /= j|.
\end{enumerate}

%if False

> propFilterLift k v z odot xs =
>   filter (keyEq k) (xs `lodot` (k,v)) == filter (keyEq k) xs `lodot` (k,v) &&
>   filter (keyEq k) xs `lodot` (k,v) == [(k, lookUpL k z xs `odot` v)]
>  where lodot = liftK odot z

%endif
\end{lemma}
%if showproofs
\begin{proof}
We prove 1. only. 
\noindent {\bf Case} |xs := []|.
\begin{spec}
   filter (keyEq k) ([] `lodot` (k,v))
=  filter (keyEq k) [(k , z `odot` v)]
=  [(k , z `odot` v)]
=  [] `lodot` (k,v)
=  filter (keyEq k) [] `lodot` (k,v) {-"~~."-}
\end{spec}

\noindent {\bf Case} |xs := xs ++ [(k,u)]|.
\begin{spec}
   filter (keyEq k) ((xs ++ [(k,u)]) `lodot` (k,v))

=  {- inductive definition of |lodot| -}

   filter (keyEq k) (xs ++ [(k , u `odot` v)])

=  filter (keyEq k) xs ++ [(k , u `odot` v)]

=  {- inductive definition of |lodot| -}

   (filter (keyEq k) xs ++ [(k , u)]) `lodot` (k,v)

=  filter (keyEq k) (xs ++ [(k , u)]) `lodot` (k,v)  {-"~~."-}
\end{spec}

\noindent {\bf Case} |xs := xs ++ [(j,u)]|, where |j /= k|.
\begin{spec}
   filter (keyEq k) ((xs ++ [(j,u)]) `lodot` (k,v))

=  {- inductive definition of |lodot| -}

   filter (keyEq k) ((xs `lodot` (k,v)) ++ [(j,u)])

=  filter (keyEq k) (xs `lodot` (k,v))

=  {- induction -}

   filter (keyEq l) xs `lodot` (k,v)
     
=  filter (keyEq k) (xs ++ [(j , u)]) `lodot` (k,v)  {-"~~."-}
\end{spec}

\end{proof}
%endif

\begin{lemma}
  \label{lemma:filter-fold}
  For all |k|, |oplus|, and |z|, we have
\begin{spec}
 filter (keyEq k) . foldl loplus [] = foldl loplus [] . filter (keyEq k) {-"~~."-}
\end{spec}
%if False

> propFilterFold :: (Eq b, Eq a) => a -> (b -> c -> b) -> b -> [(a, c)] -> Bool
> propFilterFold k oplus z ps =
>    (filter (keyEq k) . foldl loplus [] $ ps) ==
>       (foldl loplus [] . filter (keyEq k) $ ps)
>  where loplus = liftK oplus z

%endif
\end{lemma}
%if showproofs
\begin{proof}
Induction on the input.

\noindent {\bf Case} |xs := []|. Both sides reduces to |[]|.

\noindent {\bf Case} |xs := xs ++ [(k,v)]|
\begin{spec}
   filter (keyEq k) (foldl loplus [] (xs ++ [(k,v)]))

=  filter (keyEq k) (foldl loplus [] xs `loplus` (k,v))

=  {- Lemma \ref{lemma:filter-lift} -}

   filter (keyEq k) (foldl loplus [] xs) `loplus` (k,v)

=  {- induction -}

   foldl loplus [] (filter (keyEq k) xs) `loplus` (k,v)

=  foldl loplus [] (filter (keyEq k) (xs ++ [(k,v)]))

\end{spec}

\noindent {\bf Case} |xs := xs ++ [(j,v)]|, where |j /= k|.
\begin{spec}
   filter (keyEq k) (foldl loplus [] (xs ++ [(j,v)]))

=  filter (keyEq k) (foldl loplus [] xs `loplus` (j,v))

=  {- Lemma \ref{lemma:filter-lift} -}

=  filter (keyEq k) (foldl loplus [] xs)

=  {- induction -}

   foldl loplus [] (filter (keyEq k) xs)

=  foldl loplus [] (filter (keyEq k) (xs ++ [(j,v)]))

\end{spec}

\end{proof}
%endif

\begin{lemma} \label{lemma:fold-lodot-odot}
For all |k|, |odot|, and |z|, we have
\begin{spec}
  foldl lodot [] . filter (keyEq k) `app` xs =
    [(k, foldl odot z . map value . filter (keyEq k) `app` xs)]
\end{spec}
if there exists at least one |(k,v)| in |xs|. Otherwise
|foldl lodot [] . filter (keyEq k) `app` xs = []|.
%  last' z . map value . foldl loplus [] . filter (keyEq k) =
%    foldl oplus z . map value  . filter (keyEq k) {-"~~."-}

%if False

> prop3 k oplus z ps =
>   (foldl loplus [] . filter (keyEq k) $ ps)
>     == [(k , foldl oplus z . map value . filter (keyEq k) $ ps)]
>  where loplus = liftK oplus z

> wrap x = [x]

%endif

\end{lemma}
%if showproofs
\begin{proof}
  The "otherwise" part is trivially true. For the first part,
we perform an induction on the input.

\noindent{\bf Case} |xs := [(k,v)]|. Both sides reduce to |[(k,z`odot` v)]|.

\noindent{\bf Case} |xs := xs ++ [(k,v)]|.
\begin{itemize}
  \item {\bf Case} there exists at least one |[(k,u)]| in |xs|.
\begin{spec}
   foldl lodot [] (filter (keyEq k) (xs ++ [(k,v)]))
=  foldl lodot [] (filter (keyEq k) xs ++ [(k,v)])
=  foldl lodot [] (filter (keyEq k) xs) `lodot` (k,v)
=  {- induction -}
   [(k, foldl odot z . map value . filter (keyEq k) `app` xs)] `lodot` (k,v)
=  {- definition of |loplus| -}
   [(k, (foldl odot z . map value . filter (keyEq k) `app` xs) `odot` v)]
=  [(k, foldl odot z . map value . filter (keyEq k) `app` (xs ++ [(k,v)]))] {-"~~."-}
\end{spec}
  \item {\bf Case} |[(k,u)]| does not occur in |xs|.
\begin{spec}
   foldl lodot [] (filter (keyEq k) (xs ++ [(k,v)]))
=  foldl lodot [] (filter (keyEq k) xs ++ [(k,v)])
=  foldl lodot [] (filter (keyEq k) xs) `lodot` (k,v)
=  {- |filter (keyEq k) xs = []| -}
=  [] `lodot` (k,v)
=  [(k,z `odot` v)]
=  [(k, foldl odot z . map value . filter (keyEq k) `app` (xs ++ [(k,v)]))] {-"~~."-}
\end{spec}
\end{itemize}

\noindent{\bf Case} |xs := xs ++ [(j,v)]| where |j /= k|. In this case there must exists some |[(k,u)]| in |xs|.
\begin{spec}
   foldl loplus [] (filter (keyEq k) (xs ++ [(j,v)]))
=  foldl loplus [] (filter (keyEq k) xs)
=   {- induction -}
   [(k, foldl odot z . map value . filter (keyEq k) `app` xs)]
=  [(k, foldl odot z . map value . filter (keyEq k) `app` (xs ++ [(k,v)]))] {-"~~."-}
\end{spec}

\end{proof}
%endif

\begin{corollary}
As a corollary, we have that for all |k|, |odot|, and |z|,
\begin{spec}
  last_z . map value . foldl lodot [] . filter (keyEq k) =
    foldl odot z . map value . filter (keyEq k) {-"~~."-}
\end{spec}
When the input is empty or does not contain entries having key |k|, both
sides reduce to |z|.
\end{corollary}

\begin{corollary} For all |k|, |z| and |odot| we have:
\label{cor:lower-level}
  \begin{spec}
    concat . map (map value . filter (keyEq k) . foldl lodot []) =
      map (foldl odot z) . filter (not . null) . map filter (keyEq k) {-"~~."-}
  \end{spec}
%if False

> propLowerLevel k odot z xss =
>  (concat . map (map value . filter (keyEq k) . foldl lodot []) $ xss) ==
>   (map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) $ xss)
>  where lodot = liftK odot z

%endif
\end{corollary}
%if showproofs
\begin{proof} We reason:
\begin{spec}
   concat . map (map value . filter (keyEq k) . foldl lotimes [])
=  {- Lemma \ref{lemma:filter-fold} -}
   concat . map (map value . foldl loplus [] . filter (keyEq k))
\end{spec}
Let the input be |xss|. Induction.

\noindent{Case} |xss := []|. Both sides reduce to |[]|

\noindent{Case} |xss := xss ++ [xs]|
\begin{itemize}
  \item there exists at least one |(k,v)| in |xs|
  \begin{spec}
   concat . map (map value . foldl loplus [] . filter (keyEq k)) `app` (xss ++ [xs])
=  (concat . map (map value . foldl loplus [] . filter (keyEq k)) `app` xss) ++
    (map value . foldl loplus . filter (keyEq k) `app` xs)
=  {- induction-}
   (map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` xss) ++
     (map value . foldl loplus . filter (keyEq k) `app` xs)
=  {- Lemma \ref{lemma:fold-lodot-odot} -}
   (map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` xss) ++
     [foldl odot z . map value . filter (keyEq k) `app` xs]
=  map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` (xss ++ [xs])
  \end{spec}
  \item there exists no |(k,v)| in |xs|.
  \begin{spec}
   concat . map (map value . foldl loplus [] . filter (keyEq k)) `app` (xss ++ [xs])
=  {- same as above -}
   (map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` xss) ++
     (map value . foldl loplus . filter (keyEq k) `app` xs)
=  {- Lemma \ref{lemma:fold-lodot-odot} -}
   map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` xss
=  map (foldl odot z) . filter (not . null) . map (map value . filter (keyEq k)) `app` (xss ++ [xs]) {-"~~."-}
  \end{spec}
\end{itemize}
\end{proof}
%endif

Finally, the main theorem:

\begin{theorem} For all |k|, |z|, |otimes| and |oplus|, we have:
\begin{spec}
  lookUp k . aggregateByKey z otimes oplus = aggregateWithKey k z otimes oplus {-"~~."-}
\end{spec}
\end{theorem}
\begin{proof} We reason:

\begin{spec}
   lookUp k . aggregateByKey z otimes oplus
=  {- definition of |lookUp| and |aggregateByKey| -}
   last' z . concat . map (map value . filter (keyEq k)) .
     repartition . foldl loplus [] . concat . map (foldl lotimes [])
=  {-  routine naturalty laws. See below. -}
   last' z . map value . filter (keyEq k) . foldl loplus [] .
     concat . map (foldl lotimes [])
=  {- Lemma \ref{lemma:filter-fold} -}
   last' z . map value . foldl loplus [] . filter (keyEq k) .
     concat . map (foldl lotimes [])
=  {- corollary of Lemma \ref{lemma:fold-lodot-odot} -}
   foldl oplus z . map value . filter (keyEq k) . concat . map (foldl lotimes [])
=  {- naturalty, |filter p . concat = concat . map (filter p)| -}
   foldl oplus z . concat . map (map value . filter (keyEq k) . foldl lotimes [])
=  {- Corollary \ref{cor:lower-level} -}
   foldl oplus z . map (foldl otimes z) . filter (not . null) . map filter (keyEq k)
=  {- definition -}
   aggregateWithKey k z otimes oplus  {-"~~."-}
\end{spec}

The "routine naturalty laws" in the second step we need are:
\begin{itemize}
  \item |map (filter p) . repartition = repartition . filter p|,
  \item |map (map f) . repartition = repartition . map f|,
  \item |concat . partition = id|.
\end{itemize}
\end{proof}

\end{document}
