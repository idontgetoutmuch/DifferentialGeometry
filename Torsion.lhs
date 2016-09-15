% Modelling an Epidemic
% Dominic Steinitz
% 9th August 2016

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

I will define the metric of $S^{n-1}$ via pullback of the Eulcidean
metric on ${\mathbb{R}}^{n}$.

To start with we take $n$-dimension Cartesian co-ordinates:
$(x_1,x_2......x_n)$.
The metric here is $g_{ij }= δ_{ij}$, where $δ$ is the Kronecker delta.

We specify the surface patches of  $S^{n-1}$ by the parametrization  $f$:
$$x_1=r{\cos(ϕ_1)},$$

$$x_p=r{\cos(ϕ_p)}{\Pi_{m=1}^{p-1}}{\sin(ϕ_{m})},$$

$$x_n=r{\Pi_{m=1}^{n-1}}{\sin(ϕ_{m})},$$

Where $r$ is the radius of the hypersphere and the angles have the
usual range.

We see that the pullback of the Euclidean metric $g'_{ab} =
(f^*g)_{ab}$ is the metric tensor of the hypersphere. It's components
are:

$$g'_{ab} = g_{ij} {\frac{\partial{x_i}}{\partial{ϕ_a}}}
{\frac{\partial{x_j}}{\partial{ϕ_b}}} =
{\frac{\partial{x_i}}{\partial{ϕ_a}}}{\frac{\partial{x_i}}{\partial{ϕ_b}}}$$

We get $2$ cases here:

i) $a>b$ or $b>a$, For these components one obtains a series of terms
with alternating signs which vanishes, $g'_{ab}=0$ and thus all
off-diagonal components of the tensor vanish.


ii) $a=b$,

$$g'_{11}=1$$

$$g'_{aa} ={r^2}{\Pi_{m=1}^{a-1}}{\sin^2(ϕ_{m})}$$
where $2<a<{n-1}$

The determinant is very straight-forward to calculate:

$$det[g'_{ab}] = {r^2}{\Pi_{m=1}^{n-1}}g'_{mm}$$

Finally, we can write the metric of the hypersphere as:

$$g' = {r^2}{d{ϕ_{1}}}{\otimes{}d{ϕ_{1}}} +
{r^2}{\Sigma_{a=2}^{n-1}}{\Pi_{m=1}^{a-1}}{\sin^2(ϕ_{m})}{d{ϕ_{a}}}{\otimes{}d{ϕ_{a}}}
$$

Consider the sphere $S^2 \triangleq \{(x, y, z) \in \mathbb{R}^ | x^2
+ y^2 + z^2 = 1\}$

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
