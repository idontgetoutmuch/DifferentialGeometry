% A Connection with Torsion
% Dominic Steinitz
% 9th August 2016

---
bibliography: DiffGeom.bib
---

Introduction
============

In most presentations of Riemannian geometry, e.g. @o1983semi and
[Wikipedia](https://en.wikipedia.org/wiki/Fundamental_theorem_of_Riemannian_geometry),
the fundamental theorem of Riemannian geometry ("the miracle of
Riemannian geometry") is given: that for any semi-Riemannian manifold
there is a unique torsion-free metric connection. I assume partly
because of this and partly because the major application of Riemannian
geometry is General Relativity, connections with torsion are given
little if any attention.

It turns out we are all very familiar with a connection with torsion:
the Mercator projection. Some mathematical physics texts,
e.g. @Nakahara2003, allude to this but leave the details to the
reader. Moreover, this connection respects the metric induced from
Euclidean space.

The Induced Metric
==================

Before deriving the connection, we first need a metric on $S^2$. We
follow the exposition given on
[math.stackexchange.com](http://math.stackexchange.com/questions/402102/what-is-the-metric-tensor-on-the-n-sphere-hypersphere).

We can define the metric of $S^{n-1}$ via pullback of the Eulcidean
metric on ${\mathbb{R}}^{n}$.

To start with we take $n$-dimension Cartesian co-ordinates:
$(x_1,x_2......x_n)$ with the usual metric $g_{ij }= \delta_{ij}$,
where $\delta$ is the Kronecker delta.

We
[specify](https://en.wikipedia.org/wiki/N-sphere#Spherical_coordinates)
a chart $(U,x)$ on $S^{n-1}$ by $U = \{ (\phi_1, \phi_2, \ldots,
\phi_{n-1}) \, |\, \phi_1, \phi_2, \ldots, \phi_{n-2} \in (0,
\pi) \,\text{and}\, \phi_{n-1} \in (0, 2\pi) \}$ and by

$$
\begin{aligned}
x_1 &= r{\cos \phi_1} \\
x_p &= r{\cos \phi_p}{\Pi_{m=1}^{p-1}}{\sin \phi_{m}} \\
x_n &= r{\Pi_{m=1}^{n-1}}{\sin \phi_{m}}
\end{aligned}
$$

where $r$ is the radius of the hypersphere.

The pullback of the Euclidean metric $\tilde{g} = x^*g$ is the
metric tensor of the hypersphere. Its components are:

$$\tilde{g}_{ab} = g_{ij} {\frac{\partial{x_i}}{\partial{\phi_a}}}
{\frac{\partial{x_j}}{\partial{\phi_b}}} =
{\frac{\partial{x_i}}{\partial{\phi_a}}}{\frac{\partial{x_i}}{\partial{\phi_b}}}$$

1. $a \neq b$: for these components one obtains a series of terms
with alternating signs which vanishes, $\tilde{g}_{ab}=0$ and thus all
off-diagonal components of the tensor vanish.

2. $a=b$: in this case we have $\tilde{g}_{11}=r^2$ and $\tilde{g}_{aa}
={r^2}{\Pi_{m=1}^{a-1}}{\sin^2 \phi_{m}}$ where $2<a<{n-1}$.

Thus we can write the metric of the hypersphere as:

$$\tilde{g} = {r^2}{d{\phi_{1}}}{\otimes{}d{\phi_{1}}} +
{r^2}{\Sigma_{a=2}^{n-1}}{\Pi_{m=1}^{a-1}}{\sin^2 \phi_{m}}{d{\phi_{a}}}{\otimes{}d{\phi_{a}}}
$$

In the case of $S^2$ with unit radius, this gives us the familiar metric:

$$\tilde{g} = {d{\theta}}{\otimes{}d{\theta}} +
{\sin^2 \theta}{d{\phi}}{\otimes{}d{\phi}}
$$

Loxodromes (Rhumb Lines)
========================

\begin{code}
{-# OPTIONS_GHC -Wall                     #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing  #-}
{-# OPTIONS_GHC -fno-warn-type-defaults   #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind  #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}
{-# OPTIONS_GHC -fno-warn-orphans         #-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds           #-}

import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Backend.Diagrams
import Diagrams.Backend.Cairo.CmdLine
import Diagrams.Prelude hiding ( render, Renderable, sample, diff )
import Diagrams.Backend.CmdLine

import System.IO.Unsafe

import Data.Number.Symbolic
import Numeric.AD
import Numeric.AD.Internal.Reverse hiding ( var )
import Data.Reflection

import GHC.TypeLits
import Data.Proxy

import Data.Vector.Fixed
\end{code}

$$
\nabla_Y Z = \nabla_{Y^i \partial_i} Z^j \partial_j =
Y^i\nabla_{\partial_i} (Z^j \partial_j) =
Y^i(\partial_i Z^j)\partial_j + Y^i Z^j(\nabla_{\partial_i} \partial_i) =
Y^i\frac{\partial Z^j}{\partial x_i}\partial_j + Y^i Z^j\Gamma^k_{ij}\partial_k
$$

Is using the AD package worth the fight with types?

\begin{code}
foo :: forall a . Num a =>
  (forall s . Reifies s Tape => [Reverse s a -> Reverse s a]) ->
  (forall s . Reifies s Tape => [Reverse s a -> Reverse s a]) ->
  (forall s . Reifies s Tape => [[[Reverse s a -> Reverse s a]]]) ->
  [a] -> [[a]]
foo yis zis gammaijks = jacobian bar
  where
    go :: Reifies s Tape => [Reverse s a] -> [Reverse s a]
    go xs = Prelude.zipWith ($) zis (Prelude.zipWith ($) yis xs) -- [(g!!0) $ (f!!0) (xs!!0)]
    bar :: Reifies s Tape => ([Reverse s a] -> [Reverse s a])
    bar = (\[x] -> [(zis!!0) x])
    baz :: [a] -> [[a]]
    baz = jacobian bar
    urk = jacobian (\[x] -> [(zis!!0) x])

f :: Floating a => a -> a
f x = x + 1

test :: [[Sym Double]]
test = jacobian (return . f) [var "x1", var "x2"]
  where
    f [x, y] = sqrt $ x^2 + y^2

bar :: forall a . Num a =>
       forall s . Reifies s Tape => ([Reverse s a -> Reverse s a],
                                     [Reverse s a -> Reverse s a],
                                     [[[Reverse s a -> Reverse s a]]]) ->
       [a] -> [[a]]
bar (_fs, _gs, _gammass) = undefined

data Haar (a :: Nat) (b :: Nat) = Haar { unHaar :: Double -> Double }

haar :: forall n k .
        (KnownNat n, KnownNat k, (2 * k - 1 <=? 2^n - 1) ~ 'True) =>
        Haar n (2 * k - 1)
haar = Haar g where
  g t | (k' - 1) * 2 ** (-n') < t && t <= k'       * 2 ** (-n') =  2 ** ((n' - 1) / 2)
      | k'       * 2 ** (-n') < t && t <= (k' + 1) * 2 ** (-n') = -2 ** ((n' - 1) / 2)
      | otherwise                                               =  0
    where
        n' = fromIntegral (natVal (Proxy :: Proxy n))
        k' = 2 * (fromIntegral (natVal (Proxy :: Proxy k))) - 1
\end{code}

Now for example we can evaluate

\begin{code}
haar11 :: Double -> Double
haar11 = unHaar (haar :: Haar 1 1)
\end{code}

    [ghci]
    haar11 0.75

but we if we try to evaluate *haar :: Haar 1 2* we get a type error.

\begin{code}
greatCircle :: RealFloat a => (a, a) -> (a, a) -> a -> (a, a)
greatCircle (lon1, lat1) (lon2, lat2) f = (lon, lat)
  where
    d = acos(sin lat1 * sin lat2 + cos lat1 * cos lat2  * cos (lon1 - lon2))
    a= sin ((1-f)*d)/sin(d)
    b= sin(f*d)/sin(d)
    x = a*cos(lat1)*cos(lon1) +  b*cos(lat2)*cos(lon2)
    y = a*cos(lat1)*sin(lon1) +  b*cos(lat2)*sin(lon2)
    z = a*sin(lat1)           +  b*sin(lat2)
    lat=atan2 z (sqrt (x^2 + y^2))
    lon=atan2 y x
\end{code}

\begin{code}
denv :: DEnv Double
denv = unsafePerformIO $ defaultEnv vectorAlignmentFns 600 500

displayHeader :: FilePath -> Diagram B -> IO ()
displayHeader fn =
  mainRender ( DiagramOpts (Just 900) (Just 700) fn
             , DiagramLoopOpts False Nothing 0
             )

diagEstimated :: String ->
                 [(Double, Double)] ->
                 [(Double, Double)] ->
                 Diagram Cairo
diagEstimated t xs es =
  fst $ runBackend denv (render (chartEstimated t xs es) (600, 500))

chartEstimated :: String ->
              [(Double, Double)] ->
              [(Double, Double)] ->
              Renderable ()
chartEstimated title acts ests = toRenderable layout
  where

    actuals = plot_lines_values .~ [acts]
            $ plot_lines_style  . line_color .~ opaque red
            $ plot_lines_title .~ "Truncated"
            $ plot_lines_style  . line_width .~ 1.0
            $ def

    estimas = plot_lines_values .~ [ests]
            $ plot_lines_style  . line_color .~ opaque black
            $ plot_lines_title .~ "Vanilla"
            $ plot_lines_style  . line_width .~ 1.0
            $ def

    layout = layout_title .~ title
           $ layout_plots .~ [toPlot actuals, toPlot estimas]
           $ layout_y_axis . laxis_title .~ "Density"
           $ layout_y_axis . laxis_override .~ axisGridHide
           $ layout_x_axis . laxis_title .~ "Value"
           $ layout_x_axis . laxis_override .~ axisGridHide
           $ def
\end{code}

Connections
===========

The formula for the **conformal rescaling of the Levi-Civita connection** is an essential tool in Riemannian geometry, and its derivation is given in many sources. 

As Isaac Solomon and Ted Shifrin have mentioned in the comments, a slick way to derive it is to consider $f = e^{2 \omega}$ and use the Koszul formula. The result will be in the form:
$$
\nabla' _X Y = \nabla _X Y + (X \omega )Y + (Y \omega )X - g(X,Y) \operatorname{grad}\omega \tag{1}
$$

*Proof.* The **Koszul formula** (see e.g. [here][1]) gives the following expression for the Levi-Civita connection $\nabla$ of the metric $g$:
$$ 
\begin{align}
2 g(\nabla_X Y, Z) & = X \, g(Y,Z) + Y \, g(Z,X) - Z \, g(X,Y) \\ \tag{2}
&- g(X,[Y,Z]) +  g(Y,[Z,X]) + g(Z,[X,Y])
\end{align}
$$


Let $\nabla'$ be the Levi-Civita connection for the metric $\tilde{g} = e^{2\omega}g$. Substituting these objects into (2)
$$ 
\begin{align}
2 e^{2 \omega} g(\nabla'_X Y, Z) & = X \left( e^{2 \omega} g(Y,Z) \right) + Y \left( e^{2 \omega} g(Z,X) \right) - Z \left( e^{2 \omega} g(X,Y) \right) \\ 
&- e^{2 \omega} g(X,[Y,Z]) + e^{2 \omega} g(Y,[Z,X]) + e^{2 \omega} g(Z,[X,Y])
\end{align}
$$
and computing the derivatives using the product rule, we obtain
$$ 
\begin{align}
2 e^{2 \omega} g(\nabla'_X Y, Z) & = e^{2 \omega} X  g(Y,Z) + e^{2 \omega} Y  g(Z,X)  - e^{2 \omega} Z g(X,Y) \\ 
& + 2 e^{2 \omega} g(Y,Z) \, X \omega   + 2 e^{2 \omega} g(Z,X) \, Y \omega - 2  e^{2 \omega} g(X,Y) \, Z  \omega \\
&- e^{2 \omega} g(X,[Y,Z]) + e^{2 \omega} g(Y,[Z,X]) + e^{2 \omega} g(Z,[X,Y])
\end{align}
$$

In the last display we can divide both sides of the equation by $e^{2 \omega}$, which is a strictly positive function, to get
$$ 
\begin{align}
2 g(\nabla'_X Y, Z) & = X  g(Y,Z) + Y  g(Z,X)  -Z g(X,Y) \\ 
& + 2 g(Y,Z) \, X \omega   + 2 g(Z,X) \, Y \omega - 2  g(X,Y) \, Z  \omega \\
&- g(X,[Y,Z]) + g(Y,[Z,X]) +  g(Z,[X,Y])
\end{align}
$$

Using the Koszul formula (2) again we rewrite the above expression as
$$ 
\begin{align}
2 g(\nabla'_X Y, Z) & = 2 g(\nabla_X Y, Z) + 2 g(Y,Z) \, X \omega   + 2 g(Z,X) \, Y \omega - 2  g(X,Y) \, Z  \omega
\end{align}
$$
which is equivalent to (1) because vector field $Z$ is arbitrary, $g$ is non-degenerate, and $Z \omega = \mathrm{d} \omega (Z)$. Recall also that $\operatorname{grad} \omega = (\mathrm{d} \omega)^{\sharp}$.


----------

The version of this formula in terms of coordinates and the Christoffel symbols is obtained by a similar calculation, the result will be
$$
'\Gamma^{k}_{ij}=\Gamma^{k}_{ij} + \delta_{i}^{k} \partial_j \omega  + \delta_{j}^{k} \partial_i \omega - g_{i j} g^{k l} \partial_{l} \omega
$$

This can be also obtained as a consequence of (1).

[1](http://books.google.co.nz/books?id=CGk1eRSjFIIC&pg=PA61)

[2](http://math.stackexchange.com/questions/98113/conformal-transformation-of-the-curvature-and-related-quantities/98634#98634)

[3](http://math.stackexchange.com/questions/661514/relation-between-two-riemannain-connections/662991#662991)

[4](http://math.stackexchange.com/questions/761375/which-textbook-of-differential-geometry-will-introduce-conformal-transformation?rq=1)

Better: @Gadea2010

conformal metric

https://en.wikipedia.org/wiki/Killing_vector_field
https://en.wikipedia.org/wiki/Mercator_projection
http://hackage.haskell.org/package/data-reify-cse-0.0.3/docs/Data-Reify-Graph-CSE.html
http://jtobin.ca/automasymbolic-differentiation
https://www.reddit.com/r/haskell/comments/3mapnk/symbolic_differentiation_in_haskell_i_cant_even/

The mercator connection on the punctured 2-sphere

$$
\begin{aligned}
(\dot{\theta})^2 \tan^2\beta - (\dot{\phi})^2 \sin^2\theta &= 0 \\
2\dot{\theta}\ddot{\theta} \tan^2\beta - 2\dot{\phi}\ddot{\phi} \sin^2\theta - 2(\dot{\phi})^2 \sin\theta \cos\theta \dot{\theta} &= 0 \\
\ddot{\phi} + \frac{\cos\theta}{\sin\theta}\dot{\phi}\dot{\theta} = 0
\end{aligned}
$$

Introduction
============

Choose an atlas $\{(\phi_\alpha, U_\alpha) : \alpha \in
{\mathcal{A}}\}$ and a subordinate partition of unity $X_\alpha$. On
each $\phi_alpha(U_\alpha)$ define

$$
g^{(\alpha)}(\mathrm{d}x_i, \mathrm{d}x_j) = \delta_{ij}
$$

and

$$
g(u,v) = \sum_\alpha X_\alpha g^{(\alpha)}(D\phi_\alpha(u), D\phi_\alpha(v))
$$

Symmetric, positive, definite and smooth.

Consider $\mathbb{R}^3$. Let $X$, $Y$ and $Z$ be the coordinate vector
fields, and take the connection for which

$$
\begin{matrix}
\nabla_X(Y)=Z & \nabla_Y(X)=-Z \\
\nabla_X(Z)=-Y & \nabla_Z(X)=Y \\
\nabla_Y(Z)=X & \nabla_Z(Y)=-X
\end{matrix}
$$

$$
\nabla_{\frac{\partial}{\partial x_i}} {\frac{\partial}{\partial x_j}} =
\Gamma^k_{ij}\frac{\partial}{\partial x_k}
$$

$$
\ddot{\gamma}^k + \Gamma^k_{ij}\dot{\gamma}^i\dot{\gamma}^j = 0
$$

$$
\Gamma^3_{12} = 1
$$

$$
\begin{matrix}
0  & 1 & 0 \\
-1 & 0 & 0 \\
0  & 0 & 0
\end{matrix}
$$

https://en.wikipedia.org/wiki/Rhumb_line

https://en.wikipedia.org/wiki/Teleparallelism

https://books.google.co.uk/books?id=C0pJvMeKs38C&printsec=frontcover&dq=the+riddle+of+gravitation&hl=en&sa=X&redir_esc=y#v=snippet&q=mercator&f=false

The riddle of gravitation Peter Gabriel Bergmann

http://mathoverflow.net/questions/133342/torsion-and-parallel-transport
