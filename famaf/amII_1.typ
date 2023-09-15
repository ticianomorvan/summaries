#set page(
  paper: "a4",
  header: [
    #set align(center)
    #set text(16pt)
    Análisis Matemático II - Unidades 1 y 2
  ],
  footer: [
    #set align(right)
    #set text(12pt)
    #text[Ticiano Morvan -]
    #counter(page).display(
      "1 de 1",
      both: true
    )
  ]
)
#set text(12pt)
#set heading(numbering: "1.a)")
#set enum(numbering: "1)", tight: false, spacing: 16pt, indent: 12pt)
#set list(tight: false, spacing: 24pt, indent: 12pt)

= Integrales

== Integral indefinida

*Definición*: De forma general, decimos que si $I subset.eq RR$ es un intervalo y $f: I -> RR$ es una función, llamamos a la función $F: I -> RR$ como primitiva o antiderivada de $f$ en $I$ si $F'(x) = f(x) space forall x in I$.

Al conjunto de las primitivas de $f$ le llamamos #underline[integral indefinida] de $f$ y lo denotamos por:

$ integral f(x) dif x $

De manera general, satisface las siguientes *propiedades*:

- $integral 0 dif x = c$
- $integral a dot f(x) dif x = a dot integral f(x) dif x, space forall a in RR$
- $integral (f plus.minus g)(x) dif x = integral f(x) dif x plus.minus integral g(x) dif x$

*Teorema* (método de sustitución): Sean $f: (d, e) -> RR$ y $g: (a, b) -> (d, e)$ derivable en su dominio. Entonces, si $F$ es una primitiva de $f$ en $(d, e)$, $space H(x) = (F compose g)(x)$ es primitva de $h(x) = f(g(x)) dot g'(x)$ en $(a, b)$. Es decir:

$ integral f(g(x)) dot g'(x) dif x = F(g(x)) + C, space "con" c in RR space "y" space forall x in (a, b) $

*Teorema* (método de integración por partes): Si $f'$ y $g'$ son continuas, entonces

$ integral f(x) dot g'(x) dif x =  f(x) dot g(x) - integral f'(x) dot g(x) dif x $

== Integrales definidas

*Definición*: Sea $f: [a, b] -> RR$ continua y tal que $f(x) >= 0 space forall x in [a, b]$, se define el área encerrada por la curva $y = f(x)$, el eje $x$ y las rectas $x = a$ y $x = b$ por:

$ A = lim_(Delta -> 0) (sum_(k = 0)^(n - 1) m_k Delta_k) $

Llamaremos a este número la #underline[integral definida] de $f$ en $[a, b]$ y lo denotaremos por:

$ integral_(a)^b f(x) dif x $

*Observaciones*:

#list(
  [
    Si $a = b$, se define $integral_(a)^b f(x) dif x = 0$. Además, se puede probar que $integral_(a)^b f(x) dif x = - integral_(b)^a f(x) dif x$
  ],
  [
    Se puede extender a la definición a funciones que toman valores positivos y negativos, escribiendo $f(x) = f^+(x) - f^-(x)$ y haciendo
    $ integral_(a)^b f(x) dif x = integral_(a)^b f^+(x) dif x - integral_(a)^b f^-(x) dif x $
  ],
  [
    También se puede extender a funciones continuas en $[a, b]$ salvo un número #underline[finito] de puntos y siempre que $f$ esté #underline[acotada] en $[a, b]$.
  ]
)

*Propiedades*:
Sean $f,g: [a, b] -> RR$ funciones acotadas y continuas, salvo a lo sumo un número finito de puntos. Las siguientes propiedades son válidas:

#enum(
  [
    Si $f >= 0$ en [a, b] $arrow.r.double integral_(a)^b f(x) dif x >= 0$
  ],
  [
    $integral_(a)^b c dot f(x) dif x = c integral_(a)^b f(x) dif x, space forall c in RR$
  ],
  [
    $integral_(a)^b (f(x) plus.minus g(x)) dif x = integral_(a)^b f(x) dif x plus.minus integral_(a)^b g(x) dif x$
  ],
  [
    Si $d in [a, b]$, $integral_(a)^b f(x) dif x = integral_(a)^d f(x) dif x + integral_(d)^b f(x) dif x$
  ],
  [
    Si $f <= g$ en $[a, b]$, $integral_(a)^b f(x) dif x <= integral_(a)^b g(x) dif x$
  ]
)

*Teorema* (teorema fundamental del cálculo): Sea $f: [a, b] -> RR$ continua y sea $F(x) = integral_(a)^x f(t) "dt", space forall x in [a, b]$. Entonces:

#enum(
  [
    $F$ es derivable y $F'(x) = f(x) space forall x in (a, b)$. O sea, $F$ es primitiva de $f$.
  ],
  [
    (Regla de Barrow) Si $G$ es una primitiva de $f$ en $[a, b]$ entonces $ integral_(a)^b f(t) "dt" = G(b) - G(a) =^dot G(x) bar.v_(a)^b $
  ]
)

*Teorema*: Sean $f,g: [a, b] -> RR$ con $f$ continua y $g$ tal que $g(x) = f(x) space forall x in [a, b]$ salvo un $c in [a, b]$. Entonces:

$ integral_(a)^b f(x) dif x = integral_(a)^b g(x) dif x $

*Teorema* (método de sustitución): Sean $f: [c, d] -> RR$ y $g: [a, b] -> [c, d]$ tal que $f$ y $g'$ son continuas en sus respectivos dominios. Entonces si $u = g(x)$ vale que:

$ integral_(a)^b f(g(x)) dot g'(x) dif x = integral_(g(a))^g(b) f(u) "du" $

En particular, si $F$ es primitiva de $f$ tenemos que:

$ integral_(a)^b f(g(x)) dot g'(x) dif x = F(g(b)) - F(g(a)) $

*Teorema* (método de integración por partes): Sean $f$ y $g$ derivables en (a, b) y tal que $f'$ y $g'$ tienen a lo sumo un número finito de discontinuidades en $[a, b]$ y son acotadas. Entonces:

$ integral_(a)^b f(x) dot g'(x) dif x = f(x)g(x) bar.v_(a)^b - integral_(a)^b g(x) dot f'(x) dif x $

== Área entre gráficos de funciones

*Teorema*: Sea $f$ y $g$ funciones acotadas con un número finito de discontinuidades y tales que $f(x) >= g(x) >= 0 space forall x in [a, b]$ entonces el área entre los gráficos de $f$ y $g$ (y las rectas $x = a$ y $x = b$) es

$ A = integral_(a)^b (f(x) - g(x)) dif x, space "ya que" f(x) - g(x) >= 0 space forall x in [a, b] $

== Integración de funciones racionales usando fracciones simples

Teniendo $f(x) = frac(p(x), q(x))$ vamos a suponer que satisface:

#enum(
  [
    $"gr"(p) < "gr"(q)$

    Si no fuese cierto, podemos dividir $p(x)$ por $q(x)$ y así obtener:

    $ frac(p(x), q(x)) = Q(x) + frac(r(x), q(x)) $

    donde $Q(x)$ es un polinomio fácil de integrar y $r(x)$ es el resto que satisface $"gr"(r) < "gr"(q)$
  ],
  [
    El coeficiente que acompaña a la potencia de mayor grado de $q$ es $1$.

    Si no fuese cierto, podemos hacer:

    $ integral frac(p(x), q(x))
     &= frac(p(x), a_(n)x^n + a_(n -1)x^(n - 1) + dots + a_0) \
     &= frac(p(x), a_n(x^n + frac(a_(n -1), a_n)x^(n - 1) + dots frac(a_0, a_n))) \
     &= integral frac(frac(p(x), a_n), tilde(q)(x)) = integral frac(tilde(p)(x), tilde(q)(x))
    $

    Con $tilde(q)$ tal que $tilde(a_n) = 1$ (es mónico)

    Usamos el siguiente teorema para factorizar el polinomio $q(x)$

    *Teorema*: Todo polinomio mónico se puede escribir como producto de polinomios de grado $1$ y/o polinomios de grado $2$ #underline[sin] raíces reales. Es decir, vale que:

    $ "Si" q(x) = x^n + a_(n - 1)x^(n - 1) + dots + a_0, \ arrow.r.double q(x) = (x - r_1) dots (x - r_k)(x^2 + alpha_(1)x + beta_1) dots (x^2 + alpha_(2)x + beta_2) $
  ]
)

Vemos entonces que para calcular $integral frac(p(x), q(x))$ suponemos $"gr"(p) < "gr"(q)$ y $q$ mónico. Separamos en casos según la factorización de $q$:

#enum(
  [
    $q$ es producto de polinomios de grado $1$ y todos distintos tal que:

    $ q(x) = (x - r_1) dots (x - r_k), space "con" r_j eq.not r_i "si" j eq.not i $

    En tal caso buscamos constantes $A_1, dots, A_k$ (una por cada polinomio) tales que:

    $ frac(p(x), q(x)) = frac(A_1, x - r_1) + dots + frac(A_k, x - r_k), space "luego cada término" frac(A_i, (x - r_i)) "es fácil de integrar." $
  ],
  [
    $q$ es producto de polinomios de grado $1$ y todos iguales tal que:

    $ q(x) = (x - r)^k $

    En tal caso buscamos constantes $A_1, dots, A_k$ (una por cada polinomio) tales que:

    $ frac(p(x), q(x)) = frac(A_1, (x - r)) + frac(A_2, (x - r)^2) + dots + frac(A_k, (x - r)^k), space "luego cada término" frac(A_i, (x - r)^i) "es fácil de integrar." $
  ],
  [
    $q$ es producto de polinomios de grado $1$ algunos de los cuales se repiten tal que:

    $ q(x) = (x - r_1) dots (x - r_(i - 1))(x - r_i)^(k dot i) dots (x - r_n)^(k dot n) $

    En este caso aplicamos los procedimientos de los casos 1) y 2).
  ],
  [
    $q$ es producto de factores $(x - r_i)^(k dot i)$ y/o de polinomios de grado $2$ #underline[sin] raíces reales y no se repiten tal que:

    $ q(x) = (x - r_1)^(k_1) dots (x - r_n)^(k dot n) (x^2 + alpha_(1)x + beta_1) dots (x^2 + alpha_(m)x + beta_m) $

    En este caso $frac(p, q)$ se escribe como una suma donde por cada "factor lineal" aparecen tantos términos como indican los casos 1 y 2, y para cada "factor cuadrático" aparecen términos de la forma

    $ frac("B"x + C, x^2 + alpha x + beta) space "con constantes" B "y " C "a encontrar." $
  ]
)

== Integrales impropias

Extendemos la definición de integral definida para el caso en que $a "ó " b in.not RR$ o en que $f$ no esté acotada en $[a, b]$.

=== Integrales impropias de tipo I
Funciones continuas y al menos uno de los límites de integración no es finito.

*Definición*: Sea $a in RR$

#list(
  [
    Si $f$ es continua en $[a, infinity)$ definimos $integral_(a)^infinity f(x) dif x =^dot lim_(t -> infinity) integral_(a)^t f(x) dif x$ si este límite existe y es finito. En tal caso, diremos que $integral_(a)^infinity f(x) dif x$ converge, sino, diverge.
  ],
  [
    Si $f$ es continua en $(-infinity, a]$ definimos $integral_(-infinity)^a f(x) dif x =^dot lim_(t -> -infinity) integral_(t)^a f(x) dif x$ y decidimos si converge o diverge según corresponda.
  ],
  [
    Si $f$ es continua en $RR$ definimos $integral_(-infinity)^infinity f(x) dif x =^dot integral_(-infinity)^a f(x) dif x + integral_(a)^infinity f(x) dif x$ siempre que estas #underline[dos] integrales converjan y en tal caso, decimos que $integral_(-infinity)^infinity f(x) dif x$ converge, pero si alguna no converge, entonoces diremos que diverge.
  ]
)

=== Integrales impropias de tipo II
Límites de integración finitos ($a,b in RR$) pero funciones que tienen una asíntota vertical en un punto $c in [a, b]$

*Definición*:

#list(
  [
    Sea $f$ es continua en $[a, b)$ y $lim_(x -> b^-) f(x) = plus.minus infinity$. Definimos: 
    $ integral_(a)^b f(x) dif x =^dot lim_(t -> b^-) integral_(a)^t f(x) dif x $
    si este límite existe y es finito.
  ],
  [
    Sea $f$ es continua en $(a, b]$ y $lim_(x -> a^+) f(x) = plus.minus infinity$. Definimos:
    $ integral_(a)^b f(x) dif x =^dot lim_(t -> a^+) integral_(t)^b f(x) dif x $
    si este límite existe y es finito.
  ],
  [
    Sea $c in (a, b)$. Si $f$ es continua en $[a, c) union (c, b]$ y las integrales $integral_(a)^c f(x) dif x$ y $integral_(c)^b f(x) dif x$ existen y son finitos definimos:

    $ integral_(a)^b f(x) dif x =^dot integral_(a)^c f(x) dif x + integral_(c)^b f(x) dif x $
  ]
)

=== Criterio de comparación para integrales impropias

*Teorema* (criterio de comparación para integrales impropias de tipo I): Sean $f$ y $g$ funciones continuas y $a in RR$.

#list(
  [
    Si $|f(x)| <= g(x) space forall x in [a, infinity)$. Entonces:

    $ integral_(a)^infinity g(x) dif x "converge" arrow.r.double integral_(a)^infinity f(x) dif x "converge" $

    o equivalentemente:

    $ integral_(a)^infinity f(x) dif x "diverge" arrow.r.double integral_(a)^infinity g(x) dif x "diverge" $
  ],
  [
    Análogamente, si $|f(x)| <= g(x) space forall x in (-infinity, a]$. Entonces:

    $ integral_(-infinity)^a g(x) dif x "converge" arrow.r.double integral_(-infinity)^a f(x) dif x "converge" $

    o equivalentemente:

    $ integral_(-infinity)^a f(x) dif x "diverge" arrow.r.double integral_(-infinity)^a g(x) dif x "diverge" $
  ]
)

*Teorema* (criterio de comparación para integrales impropias de tipo II): Sean $f$ y $g$ funciones continuas en $[a, b)$ y tal que $|f(x)| <= g(x) space forall x in [a, b)$ y $lim_(x -> b^-) f(x) = plus.minus infinity$. Entonces:

$ integral_(a)^b g(x) dif x "converge" arrow.r.double integral_(a)^b f(x) dif x "converge" $

o equivalentemente

$ integral_(a)^b f(x) dif x "diverge" arrow.r.double integral_(a)^b g(x) dif x "diverge" $

#pagebreak()

= Sucesiones

*Definición*: una sucesión infinita de números reales es una función cuyo dominio son los naturales $NN$ y cuya imágen está incluída en $RR$. O sea $a: NN -> RR$ tal que $1 arrow.r a(1) = a_1, space 2 arrow.r a(2) = a_2$ y, en general $n arrow.r a(n) =^dot a_n$

- *Notación*: ${ a_1, a_2, a_3, dots}$, ${a_n}_(n = 1)^infinity$, ${a_n}$

*Definición*: una sucesión ${a_n}$ tiene límite $l in RR$ y se escribe:

$ lim_(n -> infinity) a_n = l $

si los términos $a_n$ se acercan a $l$ tanto como queramos al hacer $n$ suficientamente grande. Esto es:

$ lim_(n -> infinity) = l arrow.l.r.double forall epsilon > 0, space exists space n_o in NN "tq" |a_n - l| < epsilon space.quad forall n >= n_0 $ 

  - Recordemos que $|a_n - l| < epsilon arrow.l.r.double - epsilon < a_n - l < epsilon arrow.l.r.double l - epsilon < a_n < l + epsilon$

*Definición*: dada una sucesión ${a_n}$ decimos que $lim_(n -> infinity) a_n = infinity$ si los términos se hacen arbitrariamente grandes al hacer $n$ grande. Esto es:

$ forall M > 0, space exists space n_o in NN "tal que" a_n > M space.quad forall n >= n_o $

Vale análogamente para $lim_(n -> infinity) a_n = -infinity$

*Definición*: si existe $lim_(n -> infinity) a_n = l$ y $l in RR$ decimos que ${a_n}$ #underline[converge] a $l$. En los demás casos decimos que #underline[diverge].

*Teorema*: Sea ${a_n}$ y ${b_n}$ dos sucesiones convergentes y sea $c in RR$. Entonces:

#enum(
  [
    $lim_(n -> infinity) (a_n plus.minus b_n) = lim_(n -> infinity) a_n plus.minus lim_(n -> infinity) b_n$
  ],
  [
    $lim_(n -> infinity) (c dot a_n) = c dot lim_(n -> infinity) a_n$
  ],
  [
    $lim_(n -> infinity) (a_n dot b_n) = lim_(n -> infinity) a_n dot lim_(n -> infinity) b_n$
  ],
  [
    Si $lim_(n -> infinity) b_n eq.not 0$, entonces $lim_(n -> infinity) frac(a_n, b_n) = frac(lim_(n -> infinity) a_n, lim_(n -> infinity) b_n)$
  ]
)

*Teorema* (relación entre límite de funciones y sucesiones):

$ lim_(x -> infinity) f(x) = l "y " a_n = f(n) space forall n >= n_0 "para algún " n_0 in NN arrow.r.double lim_(n -> infinity) a_n = l $

Este teorema nos permite calcular límites de sucesiones aplicando la regla de *L'Hôpital*, ya que ésta solo es aplicable sobre funciones con dominio real.

*Teorema* (del "sandwich" para sucesiones):

$ a_n <= b_n <= c_n space forall n >= n_0 "para algún " n_0 in NN "y " lim_(n -> infinity) a_n = lim_(n -> infinity) c_n = l arrow.r.double lim_(n -> infinity) b_n = l $

Es decir, si una sucesión se encuentra encerrada entre dos sucesiones que convergen al mismo límite, entonces la sucesión del medio también converge a ese límite.

*Teorema*: Sea ${a_n}$ una sucesión, entonces:

$ lim_(n -> infinity) a_n = 0 arrow.l.r.double lim_(n -> infinity) |a_n| = 0 $

A partir de este teorema podemos definir los valores de convergencia de la sucesión ${r^n}$ y concluye en:

$ lim_(n -> infinity) r^n = cases(
  0 "si" r in (-1, 1),
  1 "si" r = 1,
  "diverge en los otros casos",
) $

*Teorema*: Sea ${a_n}$ tal que $lim_(n -> infinity) a_n = a$ y $f$ una función continua en $x = a$. Entonces:

$ lim_(n -> infinity) f(a_n) = f(a) $

- Ejemplo: ${e^(frac(1, n))}$, con $f(x) = e^x$ vemos que $lim_(n -> infinity) frac(1, n) = 0$. Luego, $f(x)$ es continua en $x = 0$ por lo que $lim_(n -> infinity) e^(frac(1, n)) = e^0 = 1$

*Definiciones*: decimos que la sucesión ${a_n}$ es:

- *Creciente* si $a_n <= a_(n + 1) space forall n$
- *Estrictamente creciente* si $a_n < a_(n + 1) space forall n$
- *Decreciente* si $a_(n + 1) <= a_n space forall n$
- *Estrictamente decreciente* si $a_(n + 1) < a_n space forall n$

Si ${a_n}$ es creciente o decreciente, decimos que es #underline[monótona].

*Definiciones*: decimos que la sucesión ${a_n}$ es:

- *Acotada inferiormente* si $exists M_i in RR$ tal que $M_i <= a_n space forall n in NN$
- *Acotada superiormente* si $exists M_s in RR$ tal que $a_n <= M_s space forall n in NN$
- *Acotada* si existe $M in RR$ tal que $|a_n| <= M space forall n in NN$
  - #underline[Observación]: Decimos que $M_i$ es una cota inferior de ${a_n}$ y $M_s$ es una cota superior de ${a_n}$ pero no son las únicas.

*Axioma de completitud de los números reales*: Todo conjunto no vacío de números reales que es acotado superiormente tiene una #underline[menor] cota superior en $RR$ Y todo conjunto no vacío de números reales que es acotado inferiormente tiene una #underline[mayor] cota inferior en $RR$.

*Definición*: Sea $A subset RR, A eq.not emptyset$
- Si $A$ es acotado superiormente, la menor cota superior se llama *supremo de $A$* y lo denotamos $sup(A)$
- Si $A$ es acotado inferiormente, la mayor cota inferior se llama *ínfimo de $A$* y lo denotamos $inf(A)$
- Además, si $sup(A) in A$, decimos que es el máximo de $A$ y si $inf(A) in A$, decimos que es el mínimo de $A$.

*Teorema*: Si ${a_n}$ es convergente $arrow.r.double$ es acotada. Observar que no vale la recíproca.

*Teorema*:
- Si ${a_n}$ es creciente y acotado superiormente $arrow.r.double {a_n}$ converge y $lim_(n -> infinity) a_n = l_1 = sup({a_n})$
- Si ${a_n}$ es decreciente y acotado inferiormente $arrow.r.double {a_n}$ converge y $lim_(n -> infinity) a_n = l_2 = inf({a_n})$

== Subsucesiones

Dada una sucesión ${a_n}$ podemos obtener de ésta otras sucesiones omitiendo cualquier cantidad de términos. Diremos que estas son subsucesiones de ${a_n}$.

*Definición*: una subsucesión ${a_n}$ es una sucesión de la forma:
$ {a_(n_1), a_(n_2), a_(n_3), dots} = {a_(n_j)}_(j = 1)^infinity $

Donde los $n_j in NN$ y cumplen $n_1 < n_2 < n_3 < dots < n_j$

*Teorema*: toda subsucesión de una sucesión convergente es convergente y además los límites son iguales.

- Este teorema nos permite demostrar que una sucesión no tiene límite, encontrando dos subsucesiones que converjan a distintos límites.

*Teorema* (Balzano - Weierstrass): toda sucesión acotada tiene una subsucesión convergente.

== Series

*Definición*: dada ${a_n}$ sucesión de números reales, llamaremos #underline[serie] de términos $a_n$ a $sum_(n = 1)^infinity a_n$

Para cada $k in NN$ definimos la $k"-ésima"$ #underline[suma parcial] $S_k$ de la serie $sum_(n = 1)^infinity a_n$ como $S_k =^dot a_1 + dots + a_k = sum_(n = 1)^k a_n$. Luego ${S_k}$ es una sucesión de números reales. Si el límite de la sucesión ${S_k}$ existe y es finito, decimos que la serie $sum_(n = 1)^infinity a_n$ es #underline[convergente] y definimos $sum_(n = 1)^infinity a_n =^dot S$

- Ejemplos:
  - $sum_(n = 1)^infinity n$ es divergente pues $lim_(k -> infinity) frac(k(k + 1), 2) = infinity$
  - $sum_(n = 0)^infinity (-1)^n$ es divergente pues no existe el límite de ${S_k}$, debido a que tiene dos subsucesiones que convergen a distintos límites.

*Definición*: dado $r in RR$, la serie $sum_(n = 0)^infinity r^n = 1 + r + r^2 + dots$ se llama #underline[serie geométrica].

*Teorema*:

+ Si $|r| < 1$, la serie $sum_(n = 0)^infinity r^n$ es convergente y además $sum_(n = 0)^infinity r^n = frac(1, 1 - r)$. Notar que si la serie inicia en $n = 1$, vemos que $sum_(n = 0)^infinity r^n = frac(r, 1 - r)$
+ Si $|r| >= 1$, la serie $sum_(n = 0)^infinity r^n$ es divergente.

*Propiedades de series convergentes*

*Teorema*: si $sum_(n = 1)^infinity a_n$ y $sum_(n = 1)^infinity b_n$ son series convergentes y $c in RR$ entonces $sum_(n = 1)^infinity (a_n plus.minus b_n)$ y $sum_(n = 1)^infinity c dot a_n$ son series convergentes y además:

- $sum_(n = 1)^infinity (a_n plus.minus b_n) = sum_(n = 1)^infinity a_n plus.minus sum_(n = 1)^infinity b_n$
- $sum_(n = 1)^infinity c dot a_n = c dot sum_(n = 1)^infinity a_n$

*Teorema* (criterio de la divergencia): si $sum_(n = 1)^infinity a_n$ converge, entonces $lim_(n -> infinity) a_n = 0$, valiendo su contrarrecíproca pero no su recíproca.

- Ejemplo: $sum_(n = 1)^infinity frac(1, n)$ (serie armónica)

Vale que $lim_(n -> infinity) frac(1, n) = 0$, pero vemos que $sum_(n = 1)^infinity frac(1, n)$ es divergente puesto que, si consideramos una sucesión de sumas parciales ${S_k}$, en este caso ${S_(2^j)}$. De forma general se demuestra que $S_(2^j) > 1 + j frac(1, 2)$ y como el límite de esta sucesión es $infinity$, entonces la serie es divergente.

#underline[Observación]: $sum_(n = 1)^infinity a_n "converge " arrow.l.r.double sum_(n = n_0)^infinity a_n "converge"$.

