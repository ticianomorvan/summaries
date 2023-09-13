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
#set enum(numbering: "1)", tight: false, spacing: 16pt)
#set list(tight: false, spacing: 24pt)

= Integrales

- *Definición*: Sea $I subset.eq RR$ un intervalo y $f: I -> RR$ una función, definimos que $F: I -> RR$ es una antiderivada o primitiva de $f$ en $I$ si $F'(x) = f(x) space forall x in I$. Notar que las primitivas #underline[no] son únicas.

- *Teorema*: Si $F$ es una primitiva de $f$ en $I$ entonces toda primitiva de $f$ en $I$  es de la forma $F(x) + c$, para algún $c in RR$.

== Integrales indefinidas

- *Definición*: Dado $I subset.eq RR$ y $f: I -> RR$, se llama #underline[integral indefinida] de $f$ al #underline[conjunto de todas las primitivas] de $f$ y se denota

$ integral f(x) "dx" $

- *Propiedades*:
  - $integral 0 "dx" = c$
  - $integral a dot f(x) "dx" = a dot integral f(x) "dx", space forall a in RR$
  - $integral (f plus.minus g)(x) "dx" = integral f(x) "dx" plus.minus integral g(x) "dx"$

- *Teorema* (método de sustitución): Sean $f: (d, e) -> RR$ y $g: (a, b) -> (d, e)$ derivable en su dominio. Entonces, si $F$ es una primitiva de $f$ en $(d, e)$, $H(x) = (F compose g)(x)$ es primitva de $h(x) = f(g(x)) dot g'(x)$ en $(a, b)$. Es decir:

$ integral f(g(x)) dot g'(x) "dx" = F(g(x)) + C, space "con" c in RR space "y" space forall x in (a, b) $

- *Teorema* (método de integración por partes): Si $f'$ y $g'$ son continuas, entonces

$ integral f(x) dot g'(x) "dx" =  f(x) dot g(x) - integral f'(x) dot g(x) "dx" $

#align(center)[
  o equivalentemente, usando notación de sustitución tal que $u = f(x)$, $v = g(x)$, $"du" = f'(x) "dx"$ y $"dv" = g'(x) "dx"$:
]

$ integral u dot "dv" =  u dot v - integral u dot "dv" $

== Integrales definidas

- *Definición*: Sea $f: [a, b] -> RR$ continua y tal que $f(x) >= 0 space forall x in [a, b]$, se define el área encerrada por la curva $y = f(x)$, el eje $x$ y las rectas $x = a$ y $x = b$ por:

$ A = lim_(Delta -> 0) (sum_(k = 0)^(n - 1) m_k Delta_k) $

Llamaremos a este número la #underline[integral definida] de $f$ en $[a, b]$ y lo denotaremos por:

$ integral_(a)^b f(x) "dx" $

- *Observaciones*:
  #list(
    [
      Si $a = b$, se define $integral_(a)^b f(x) "dx" = 0$. Además, se puede probar que $integral_(a)^b f(x) "dx" = - integral_(b)^a f(x) "dx"$
    ],
    [
      Se puede extender a la definición a funciones que toman valores positivos y negativos, escribiendo $f(x) = f^+(x) - f^-(x)$ y haciendo
      $ integral_(a)^b f(x) "dx" = integral_(a)^b f^+(x) "dx" - integral_(a)^b f^-(x) "dx" $
    ],
    [
      También se puede extender a funciones continuas en $[a, b]$ salvo un número #underline[finito] de puntos y siempre que $f$ esté #underline[acotada] en $[a, b]$.
    ]
  )

- *Propiedades*:
Sean $f,g: [a, b] -> RR$ funciones acotadas y continuas, salvo a lo sumo un número finito de puntos. Las siguientes son válidas:

  #enum(
    [
      Si $f >= 0$ en [a, b] $arrow.r.double integral_(a)^b f(x) "dx" >= 0$
    ],
    [
      $integral_(a)^b c dot f(x) "dx" = c integral_(a)^b f(x) "dx", space forall c in RR$
    ],
    [
     $integral_(a)^b (f(x) plus.minus g(x)) "dx" = integral_(a)^b f(x) "dx" plus.minus integral_(a)^b g(x) "dx"$
    ],
    [
      Si $d in [a, b]$, $integral_(a)^b f(x) "dx" = integral_(a)^d f(x) "dx" + integral_(d)^b f(x) "dx"$
    ],
    [
      Si $f <= g$ en $[a, b]$, $integral_(a)^b f(x) "dx" <= integral_(a)^b g(x) "dx"$
    ]
  )

- *Teorema* (teorema fundamental del cálculo): Sea $f: [a, b] -> RR$ continua y sea $F(x) = integral_(a)^x f(t) "dt", space forall x in [a, b]$. Entonces:

  #enum(
    [
      $F$ es derivable y $F'(x) = f(x) space forall x in (a, b)$. O sea, $F$ es primitiva de $f$.
    ],
    [
      Si $G$ es una primitiva de $f$ en $[a, b]$ entonces $ integral_(a)^b f(t) "dt" = G(b) - G(a) =^dot G(x) bar.v_(a)^b $
      (Esta parte se conoce como *Regla de Barrow*)
    ]
  )

- *Teorema*: Sean $f,g: [a, b] -> RR$ con $f$ continua y $g$ tal que $g(x) = f(x) space forall x in [a, b]$ salvo un $c in [a, b]$. Entonces:

$ integral_(a)^b f(x) "dx" = integral_(a)^b g(x) "dx" $

- *Teorema* (método de sustitución): Sean $f: [c, d] -> RR$ y $g: [a, b] -> [c, d]$ tal que $f$ y $g'$ son continuas en sus respectivos dominios. Entonces si $u = g(x)$ vale que:

$ integral_(a)^b f(g(x)) dot g'(x) "dx" = integral_(g(a))^g(b) f(u) "du" $

En particular, si $F$ es primitiva de $f$ tenemos que:

$ integral_(a)^b f(g(x)) dot g'(x) "dx" = F(g(b)) - F(g(a)) $

- *Teorema* (método de integración por partes): Sean $f$ y $g$ derivables en (a, b) y tal que $f'$ y $g'$ tienen a lo sumo un número finito de discontinuidades en $[a, b]$ y son acotadas. Entonces:

$ integral_(a)^b f(x) dot g'(x) "dx" = f(x)g(x) bar.v_(a)^b - integral_(a)^b g(x) dot f'(x) "dx" $

Vale de igual manera las sustituciones de $u = f(x)$ y $v = g(x)$ como en el método para las integrales indefinidas.

== Área entre gráficos de funciones

- *Teorema*: Sea $f$ y $g$ funciones acotadas con un número finito de discontinuidades y tales que $f(x) >= g(x) >= 0 space forall x in [a, b]$ entonces el área entre los gráficos de $f$ y $g$ (y las rectas $x = a$ y $x = b$) es

$ A = integral_(a)^b (f(x) - g(x)) "dx", space "ya que" f(x) - g(x) >= 0 space forall x in [a, b] $

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

- *Definición*: Sea $a in RR$
  #list(
    [
      Si $f$ es continua en $[a, infinity)$ definimos $integral_(a)^infinity f(x) "dx" =^dot lim_(t -> infinity) integral_(a)^t f(x) "dx"$ si este límite existe y es finito. En tal caso, diremos que $integral_(a)^infinity f(x) "dx"$ converge, sino, diverge.
    ],
    [
      Si $f$ es continua en $(-infinity, a]$ definimos $integral_(-infinity)^a f(x) "dx" =^dot lim_(t -> -infinity) integral_(t)^a f(x) "dx"$ y decidimos si converge o diverge según corresponda.
    ],
    [
      Si $f$ es continua en $RR$ definimos $integral_(-infinity)^infinity f(x) "dx" =^dot integral_(-infinity)^a f(x) "dx" + integral_(a)^infinity f(x) "dx"$ siempre que estas #underline[dos] integrales converjan y en tal caso, decimos que $integral_(-infinity)^infinity f(x) "dx"$ converge, pero si alguna no converge, entonoces diremos que diverge.
    ]
  )

=== Integrales impropias de tipo II
Límites de integración finitos ($a,b in RR$) pero funciones que tienen una asíntota vertical en un punto $c in [a, b]$

- *Definición*:
  #list(
    [
      Sea $f$ es continua en $[a, b)$ y $lim_(x -> b^-) f(x) = plus.minus infinity$. Definimos: 
      $ integral_(a)^b f(x) "dx" =^dot lim_(t -> b^-) integral_(a)^t f(x) "dx" $
      si este límite existe y es finito.
    ],
    [
      Sea $f$ es continua en $(a, b]$ y $lim_(x -> a^+) f(x) = plus.minus infinity$. Definimos:
      $ integral_(a)^b f(x) "dx" =^dot lim_(t -> a^+) integral_(t)^b f(x) "dx" $
      si este límite existe y es finito.
    ],
    [
      Sea $c in (a, b)$. Si $f$ es continua en $[a, c) union (c, b]$ y las integrales $integral_(a)^c f(x) "dx"$ y $integral_(c)^b f(x) "dx"$ existen y son finitos definimos:

      $ integral_(a)^b f(x) "dx" =^dot integral_(a)^c f(x) "dx" + integral_(c)^b f(x) "dx" $
    ]
  )

=== Criterio de comparación para integrales impropias

- *Teorema* (criterio de comparación para integrales impropias de tipo I): Sean $f$ y $g$ funciones continuas y $a in RR$.
  #list(
    [
      Si $|f(x)| <= g(x) space forall x in [a, infinity)$. Entonces:

      $ integral_(a)^infinity g(x) "dx" "converge" arrow.r.double integral_(a)^infinity f(x) "dx" "converge" $

      o equivalentemente:

      $ integral_(a)^infinity f(x) "dx" "diverge" arrow.r.double integral_(a)^infinity g(x) "dx" "diverge" $
    ],
    [
      Análogamente, si $|f(x)| <= g(x) space forall x in (-infinity, a]$. Entonces:

      $ integral_(-infinity)^a g(x) "dx" "converge" arrow.r.double integral_(-infinity)^a f(x) "dx" "converge" $

      o equivalentemente:

      $ integral_(-infinity)^a f(x) "dx" "diverge" arrow.r.double integral_(-infinity)^a g(x) "dx" "diverge" $
    ]
  )

- *Teorema* (criterio de comparación para integrales impropias de tipo II): Sean $f$ y $g$ funciones continuas en $[a, b)$ y tal que $|f(x)| <= g(x) space forall x in [a, b)$ y $lim_(x -> b^-) f(x) = plus.minus infinity$. Entonces:

$ integral_(a)^b g(x) "dx" "converge" arrow.r.double integral_(a)^b f(x) "dx" "converge" $

o equivalentemente

$ integral_(a)^b f(x) "dx" "diverge" arrow.r.double integral_(a)^b g(x) "dx" "diverge" $

#pagebreak()

= Sucesiones