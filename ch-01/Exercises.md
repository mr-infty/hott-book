---
toc: true
header-includes:
- \usepackage{textcomp}
---

# Exercises Chapter One

## Exercise 1.1
> Given functions $f: A \rightarrow B$ and $g: B \rightarrow C$, define their
> **composite** $g\circ f: A \rightarrow C$. Show that we have $h \circ (g\circ
> f) \equiv (h\circ g) \circ f$.

* * *
Of course we put

$$ g \circ f :\equiv \labstt{\ttt{x}}{A}{g(f(\ttt{x}))}. $$

Although not explicitly asked for, let us first derive the typing judgement
$g\circ f : A \rightarrow C$ before we derive the (judgemental) associativity.
To make this more fun^[Contrary to intuition, the fun of doing mathematics in
type theory lies (for me at least) in *actually doing things formally*,
**preferrably on a computer**, rather than merely asserting that that's possible. Note
that the apparent awkwardness that lies in doing mathematics formally is the
same awkwardness that lies in writing down computer programs using "pen and
paper"; both activities are only joyful when done on a computer.],
let's do this formally, using the derivation rules presented in the Appendix (A.2).

Before we start doing this however, some remarks are in order. Even though the
type system is presented quite formally in A.2, it still leaves a few things
undefined. For example (cf. A.2.11), this system does not support *named* or
*defined* *constants* as presented. This is in contrast with the first, less
formal presentation of the type system in A.1. So technically, it doesn't make
sense to try to derive the above judgement since $g \circ f$ isn't even a term
in that system.

In the following, we shall ignore this rather technical point
and simply pretend that deriving the judgement $g\circ f : A \rightarrow C$ is equivalent to deriving
the judgement

$$ \labstt{\ttt{x}}{A}{g(f(\ttt{x}))} : A \rightarrow C.$$

With that being said, $g\circ f: A \rightarrow C$ has the following formal
derivation^[Unfortunately due to width constraints of the page, the derivation
tree is rendered in a non-standard way, with the premises of some rules being
rendered *on top of each other* instead of horizontally on one line. In
particular, the whole derivation tree ends with three (identical) premises, namely $\Gamma, x : A\ \texttt{ctx}$.]

\begin{gather*}
   \inferrule*[right=\text{$\Pi$-INTRO}] {
      \inferrule*[right=\text{$\Pi$-ELIM}] {
         \inferrule*[right=\text{Vble}] {
            \Gamma, \ttt{x} : A\ \texttt{ctx}
         } {
            \Gamma, \ttt{x} : A \vdash g : B \rightarrow C
         } \\
         \inferrule*[right=\text{$\Pi$-ELIM}] {
            \inferrule*[right=\text{Vble}] {
               \Gamma, \ttt{x} : A\ \texttt{ctx}
            } {
               \Gamma, \ttt{x} : A \vdash f : A \rightarrow B
            } \\
            \inferrule*[right=\text{Vble}] {
               \Gamma, \ttt{x} : A\ \texttt{ctx}
            } {
               \Gamma, \ttt{x} : A \vdash \ttt{x} : A
            }
         } {
            \Gamma, \ttt{x} : A \vdash f(\ttt{x}) : B
         }
      } {
         \Gamma, x : A \vdash g(f(\ttt{x})) : C
      }
   } {
      \Gamma \vdash \labstt{\ttt{x}}{A}{g(f(\ttt{x}))} : A \rightarrow C
   },
\end{gather*}
where we have put the abbreviation

$$\Gamma := f : A \rightarrow B,\ g : B \rightarrow C.$$
The remaining premise

$$\Gamma, \ttt{x} : A\ \texttt{ctx}$$
can be further reduced using the rules $\text{ctx-EMP}$, $\text{ctx-EXT}$ and
$\text{$\Pi$-FORM}$ to the two judgements

$$A : \mathcal{U}_0, \quad B : \mathcal{U}_0.$$

Let us now prove the judgemental associativity^[Here and in the following, we
will often abbreviate equality judgements like $a \equiv b : B$ by suppressing
the type $B$ in the notation. Note however, that the type really is an integral
part of equality judgements in Martin-Löf type theory.]

$$h \circ (g \circ f) \equiv (h \circ g) \circ f,$$

or rather,

$$\labstt{\ttt{x}}{A}{h(\labstt{\ttt{x}}{A}{g(f(\ttt{x}))}(\ttt{x}))} \equiv \labstt{\ttt{x}}{A}{(\labstt{\ttt{x}}{A}{h(g(\ttt{x})))(f(\ttt{x}))}}.$$

We will do this by rewriting both sides of the equation (one side at a time),
meaning that in each step we replace a subterm---indicated by underlining---with
another one that can be proved to be judgementally equal to it via one of the
rules of appendix A.2. The rule being used will be indicated below.

Note that replacing a subterm by something that's judgementally
equal to it results in a term that's still judgementally equal to the original
term; this follows from the fact^[Actually, it's not entirely clear whether this holds true for the rules given in appendix A.2; see issue #0.] that judgemental equality is a congruence relation with respect to eliminators (and constructors) of types.

Finally note that the application of the rules in A.2 usually requires some
typing judgement as a premise; we will therefore make implicit use of the rule

$$\inferrule{f : A \rightarrow B \\ g : B \rightarrow C}{g\circ
f : A \rightarrow C}$$
that we have already established, in the following.

With that being said, the equality is derived as follows.

\begin{align*}
   \labstt{\ttt{x}}{A}{h(\underline{\labstt{\ttt{x}}{A}{g(f(\ttt{x}))}(\ttt{x})})} & \equiv \labstt{\ttt{x}}{A}{(\labstt{\ttt{x}}{A}{h(g(\ttt{x})))(f(\ttt{x}))}} \\
   &\text{\footnotesize($\Pi$-COMP)} \\
   \labstt{\ttt{x}}{A}{h(g(f(\ttt{x})))} & \equiv \labstt{\ttt{x}}{A}{\underline{(\labstt{\ttt{x}}{A}{h(g(\ttt{x}))})(f(\ttt{x}))}} \\
   &\text{\footnotesize($\Pi$-COMP)} \\
   \labstt{\ttt{x}}{A}{h(g(f(\ttt{x})))} & \equiv \labstt{\ttt{x}}{A}{h(g(f(\ttt{x})))} \\
\end{align*}

Finally, the last (tautological) equality is derivable from the basic
structural rules in A.2.2 (again making use of the typing judgements we derived
earlier).

## Exercise 1.2
> Derive the recursion principle for products $\rec_{A\times B}$ using only
> the projections, and verify that the definitional equalities are valid. Do the
> same for $\Sigma$-types.

* * *
Before we begin, some nitpicking about the notation $\rec_{A\times B}$ is in
order. Namely, $\rec_{A\times B}$ is merely *syntactic sugar* for something like
$\operatorname{\text{$\times$-rec}}(A)(B)$, with
$\operatorname{\text{$\times$-rec}}$ being a primitive constant in our type
theory, together with the assumed typing judgement^[Note that this only gives us the
recursor for one fixed universe $\mathcal{U}$; therefore, one might want to
introduce a separate recursor symbol for every universe, or have it depend also
on the universe in the case when universes form a type family.]

$$\operatorname{\text{$\times$-rec}} : \prod_{A,B:\mathcal{U}}
\prod_{C:\mathcal{U}} (A \rightarrow B \rightarrow C) \rightarrow A\times
B \rightarrow C.$$

In particular, neither is $\rec_{A\times B}$ a primitive symbol (separately defined for
any two terms $A$ and $B$) nor is it of the form $t(A\times B)$ for some term $t$.

With that being said, we can define

$$\rec_{A\times B} : \prod_{C:\mathcal{U}} (A \rto B \rto C) \rto A\times
B \rto C$$

using the projections^[the types $A$, $B$ are suppressed in the notation, but
$\pr_1$ should be read as $\pr_1(A)(B)$]

\begin{align*}
\pr_1 & : A \times B \rto A \\
\pr_2 & : A \times B \rto B
\end{align*}

as

$$\rec_{A\times B}(C, g, p) \jdef g(\pr_1(p), \pr_2(p)).$$

To verify the definitional equation (i.e. computational rule)

$$\rec_{A\times B}(C, g, (a, b)) \equiv g(a)(b)$$
as well as the equations^[we suppress the type annotation in the lambda
abstractions below, for better readability]

\begin{align*}
   \pr_1 & \equiv \rec_{A\times B}(A,
   \labst{\ttt{a}}{\labst{\ttt{b}}{\ttt{a}}}) \\
   \pr_2 & \equiv \rec_{A\times B}(A,
   \labst{\ttt{a}}{\labst{\ttt{b}}{\ttt{b}}}),
\end{align*}
we proceed as in the solution of exercise 1.1, by rewriting both sides of the
relevant judgemental equation, one side at a time, indicating the subterm
that's being rewritten as well as the derivational rule being used in that
rewrite step.

\begin{align*}
\underline{\rec_{A\times B}(C, g, (a, b))} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(\underline{\pr_1((a,b))}, \underline{\pr_2((a,b))}) & \equiv g(a)(b) \\
   &\text{\footnotesize(comp. rule for $\pr$)} \\
   \underline{g(a, b)} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(a)(b) & \equiv g(a)(b)
\end{align*}

\begin{align*}
   \pr_1 & \equiv \underline{\rec_{A\times B}(A, \labst{\ttt{a}}{\labst{\ttt{b}}{\ttt{a}}})} \\
   &\text{\footnotesize(definition)} \\
   \pr_1 & \equiv
   \labst{\ttt{p}}{\underline{(\labst{\ttt{a}}{\labst{\ttt{b}}{\ttt{a}}})(\pr_1(\ttt{p}), \pr_2(\ttt{p}))}} \\
   &\text{\footnotesize(definition)} \\
   \pr_1 & \equiv \labst{\ttt{p}}{\underline{(\labst{\ttt{a}}{\labst{\ttt{b}}{\ttt{a}}})(\pr_1(\ttt{p}))}(\pr_2(\ttt{p}))} \\
   &\text{\footnotesize($\Pi$-COMP)} \\
   \pr_1 & \equiv \labst{\ttt{p}}{\underline{(\labst{\ttt{b}}{\pr_1(\ttt{p})})(\pr_2(\ttt{p}))}} \\
   &\text{\footnotesize($\Pi$-COMP)} \\
   \pr_1 & \equiv \underline{\labst{\ttt{p}}{\pr_1(\ttt{p})}} \\
   &\text{\footnotesize($\Pi$-UNIQ)} \\
   \pr_1 & \equiv \pr_1
\end{align*}
Similarly, by rewriting one can reduce the equation for $\pr_2$ to the
tautology $\pr_2 \equiv \pr_2$.

Now let's do this whole shebang for $\Sigma$-types. As before, we define
$$\Srec{A}{B} : \prod_{C:\mathcal{U}} \left(\prod_{\ttt{x} : A} B(\ttt{x})
\rto C\right) \rto \left(\sum_{\ttt{x} : A} B(\ttt{x})\right) \rto C$$
by
$$\Srec{A}{B}(C, g, p) \jdef g(\pr_1(p), \pr_2(p)).$$
The computational rule for the $\Sigma$-recursor is then proven by the same
formal calculation as before.
\begin{align*}
   \underline{\Srec{A}{B}(C, g, (a, b))} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(\underline{\pr_1((a,b))}, \underline{\pr_2((a,b))}) & \equiv g(a)(b) \\
   &\text{\footnotesize(comp. rule for $\pr$)} \\
   \underline{g(a, b)} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(a)(b) & \equiv g(a)(b)
\end{align*}

\begin{center} \textbf{--------- A tangent ---------} \end{center}

Just to make things clear, let's spell out what the above formal calculation
is supposed to mean.
In the last line, we have arrived at a "judgement", which is meant to
abbreviate the following judgement in Martin-Löf type theory.

$$A : \mathcal{U}, B : A \rightarrow \mathcal{U}, C : \mathcal{U},
 g : \prod_{\ttt{x}:A} B(\ttt{x}) \rto C, a : A, b : B(a) \vdash g(a)(b) \equiv g(a)(b) : C$$
This is pretty obvious. However, there is a slight problem with this. Namely,
this is *not* a well-formed judgement in Martin-Löf type theory because $A,B,C,g,a,b$ were taken to be
*meta-theoretical* variables standing for arbitrary *terms* in the object language.
But, by definition a context must be of the form
$$x_1 : A_1, x_2 : A_2, \ldots, x_n : A_n$$
for some pair-wise distinct *variables* $x_i$ in the object language.

However, we can repair this in one of two ways. The first way would be to keep
the meta-variables but introduce a context $\Delta$, making the
meta-theoretical assumption that the judgements
\begin{align*}
\Delta & \vdash A : \mathcal{U} \\
\Delta & \vdash B : A \rto \mathcal{U} \\
\Delta & \vdash C : \mathcal{U} \\
\Delta & \vdash g : \prod_{\ttt{x}:A} B(x) \\
\Delta & \vdash a : A \\
\Delta & \vdash b : B(a)
\end{align*}
are derivable; in this case, our claim would be that the judgement
$$\Delta \vdash g(a)(b) \equiv g(a)(b) : C$$
is also derivable.

The second way would be to replace the meta-variables $A,B,C,g,a,b$ by
object-variables $\ov{A}, \ov{B}, \ov{C}, \ov{g}, \ov{a}, \ov{b}$. Then
$$\ov{A} : \mathcal{U}, \ov{B} : \ov{A} \rightarrow \mathcal{U}, \ov{C} : \mathcal{U},
 \ov{g} : \prod_{\ttt{x}:\ov{A}} \ov{B}(\ttt{x}) \rto \ov{C}, \ov{a} : \ov{A}, \ov{b} : \ov{B}(\ov{a}) \vdash \ov{g}(\ov{a})(\ov{b}) \equiv \ov{g}(\ov{a})(\ov{b}) : \ov{C}$$
is a well-formed judgement.

Now in either case, the "judgement" with which we end is tautological^[but not
trivial, as it implicitly contains the typing "judgement" $g(a)(b) : C$] and derivable in "the obvious way\texttrademark", which is why our formal calculation ends there.

By using the transitivity rule
$$\inferrule{\Gamma \vdash a \equiv b : A \\ \Gamma \vdash b \equiv
c : A}{\Gamma \vdash a \equiv c : A},$$
we then successively derive the judgements from bottom to top using the
equality judgements between the left resp. right sides of two consecutive
lines. For example, to get from the bottom line to the third line, we apply
transitivity to the "judgements"
$$g(a)(b) \equiv g(a)(b) \quad\text{and}\quad g(a,b) \equiv g(a)(b);$$
of course in this case, the application of transitivity is trivial because what
we derive is already assumed. Similarly, to get from the third to the second
line, we use transitivity on
$$g(a,b) \equiv g(a)(b) \quad\text{and}\quad g(\pr_1((a,b)),\pr_2((a,b)))
\equiv g(a,b).$$

Justifying the "definitional" equality
$$g(a,b) \equiv g(a)(b)$$
(disregarding for a moment the problem of interpreting this "judgement" as an actual judgement in
type theory) is a bit tricky. Now of course, this should be trivial, but to really justify
*why* (and *how*^[i.e. in which theory, the object theory or some meta theory, this equation should hold]) it's trivial, we must be explicit about the syntax of terms and
types. This is tedious (and not completely straightforward), so you'll have
a hard time finding any source where this is done (in the HoTT book, there's
a *sketch* for the version of type theory presented in appendix A.1 though).

For example, you have to decide whether you actually want $g(a,b)$ to be a term
in your syntax, i.e. whether you want to have two different ways to write
function application. You probably don't, because you want to be your type
theory to be clean and easy to reason about. Let us therefore agree that
$g(a,b)$ is "notation" in the sense that the reader is supposed to substitute
with $g(a)(b)$ *before* even trying to interpret it as a judgement of
Martin-Löf type theory. In other words, when we write down things, we use
another (higher-level) language that should be "compiled down" to actual
Martin-Löf type theory.

Implicit in this convention is the assumption that the
"rewrite system" defined by the "notational convention"
$$f(a_1,\ldots,a_n) \equiv f(a_1)\ldots (a_n)$$
is *terminating* and *confluent* (i.e. *convergent*), i.e. that by applying
this rule repeatedly in any way, we will always arrive at a term which doesn't
have $k$-ary function application terms as subterms with $k \geq 2$ after a
finite number of steps, and irrespective of the way we do it, we always end up
with the same term. For example, we can rewrite $g(a,b)(c,d)$ as

$$\underline{g(a,b)}(c,d) \leadsto \underline{g(a)(b)(c,d)} \leadsto
g(a)(b)(c)(d)$$
or as

$$\underline{g(a,b)(c,d)} \leadsto \underline{g(a,b)}(c)(d) \leadsto
g(a)(b)(c)(d),$$
both leading to the same normal form $g(a)(b)(c)(d)$. This seems obvious but
still requires proof. In particular, if we add more such conventions.

Let us not deal with these "implementation details" and instead just assume
that everything works out fine. The above formal computation then collapses to

\begin{align*}
   \underline{\Srec{A}{B}(C)(g)((a, b))} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(\underline{\pr_1((a,b))})(\underline{\pr_2((a,b))}) & \equiv g(a)(b) \\
   &\text{\footnotesize(comp. rule for $\pr$)} \\
   \underline{g(a)(b)} & \equiv g(a)(b) \\
   &\text{\footnotesize(definition)} \\
   g(a)(b) & \equiv g(a)(b).
\end{align*}

Ignoring the last, now trivial step, let us show in detail how you get from the
third to the second "judgement". To be concrete, let us interpret these
"judgements" as judgements using the object-variable fix.

The derivation---which we write in linear form because writing it as a tree would
be a total mess---goes as follows, where we abbreviate

$$\Delta = \ov{A} : \mathcal{U}, \ov{B} : \ov{A} \rightarrow \mathcal{U}, \ov{C} : \mathcal{U},
 \ov{g} : \prod_{\ttt{x}:\ov{A}} \ov{B}(\ttt{x}) \rto \ov{C}, \ov{a} : \ov{A}, \ov{b} : \ov{B}(\ov{a}).$$

\begin{align*}
\text{(1)} && \Delta & \vdash \ov{g}(\ov{a})(\ov{b}) \equiv \ov{g}(\ov{a})(\ov{b}) : \ov{C} && \\
\text{(2)} && \Delta & \vdash \pr_1((\ttt{a},\ttt{b})) \equiv \ttt{a} : \ttt{A} && \text{comp. rule for $\pr$ (and $\text{Wkg}_1$)} \\
\text{(3)} && \Delta & \vdash \pr_2((\ttt{a},\ttt{b})) \equiv \ttt{b} : \ttt{B}(\ttt{a}) && \text{comp. rule for $\pr$ (and $\text{Wkg}_1$)} \\
\text{(4)} && \Delta & \vdash \ov{g}(\ov{a}) \equiv
\ov{g}(\pr_1((\ov{a},\ov{b}))) : \ov{B}(\ov{a}) \rto C && \text{congruence on
(2)} \\
\text{(5)} && \Delta & \vdash \ov{g}(\ov{a})(\pr_2((\ov{a},\ov{b}))) \equiv
\ov{g}(\ov{a})(\ov{b}) : \ov{C} && \text{congruence on (3)} \\
\text{(6)} && \Delta & \vdash \ov{g}(\ov{a})(\pr_2((\ov{a},\ov{b}))) \equiv
\ov{g}(\pr_1((\ov{a},\ov{b})))(\pr_2((\ov{a},\ov{b}))) : C && \text{congruence
on (4)} \\
\text{(7)} && \Delta & \vdash \ov{g}(\pr_1((\ov{a},\ov{b})))(\pr_2((\ov{a},\ov{b}))) \equiv
\ov{g}(\ov{a})(\pr_2((\ov{a},\ov{b}))) : C && \text{$\equiv$-symmetry on (6)} \\
\text{(8)} && \Delta & \vdash \ov{g}(\pr_1((\ov{a},\ov{b})))(\pr_2((\ov{a},\ov{b}))) \equiv \ov{g}(\ov{a})(\ov{b}) : C && \text{$\equiv$-transitivity on (5) and (7)} \\
\text{(9)} && \Delta & \vdash \ov{g}(\pr_1((\ov{a},\ov{b})))(\pr_2((\ov{a},\ov{b}))) \equiv \ov{g}(\ov{a})(\ov{b}) : C && \text{$\equiv$-transitivity on (1) and (8)}
\end{align*}

Since the judgement with which we start is tautological, the last step of this
derivation is of course superfluous; it's only included here to preserve the
form of the argument in the general case.

The *congruence rules* alluded to in the above derivation are the following,
which aren't explicitly stated in appendix A.2 but (perhaps) alluded to in the
remark at the end of A.2.2 ("Additionally [...] we assume rules stating that
each constructor preserves definitional equality...").

$$\inferrule{\Gamma \vdash A:\mathcal{U} \\ \Gamma \vdash B : A \rto
\mathcal{U} \\ \Gamma \vdash f : \PiType{A}{B} \\ \Gamma \vdash a \equiv a' : A}{\Gamma \vdash f(a) \equiv f(a') : B(a)}$$

$$\inferrule{\Gamma \vdash A:\mathcal{U} \\ \Gamma \vdash B : A \rto
\mathcal{U} \\ \Gamma \vdash a : A \\ \Gamma \vdash f \equiv f' : \PiType{A}{B}}{\Gamma \vdash f(a) \equiv f'(a) : B(a)}.$$

From the first rule, one can derive the following as a special case: 

$$\inferrule{\Gamma \vdash A:\mathcal{U} \\ \Gamma \vdash B : A \rto
\mathcal{U} \\ \Gamma \vdash a \equiv a' : A}{\Gamma \vdash B(a) \equiv B(a') : \mathcal{U}}.$$

\begin{center} \textbf{--------- End of tangent ---------} \end{center}

Similarly, one "proves" the equations

\begin{align*}
   \pr_1 & \equiv \Srec{A}{B}(A, \labst{\ov{a}}{\labst{\ov{b}}{\ov{a}}}) \\
   \pr_2 & \equiv \Srec{A}{B}(B, \labst{\ov{a}}{\labst{\ov{b}}{\ov{b}}})
\end{align*}

using the exact same formal calculation as before.

## Exercise 1.3
> Derive the induction principle for products $\IndProd{A}{B}$ using only
> the projections and the propositional uniqueness principle $\UniqProd{A}{B}$.
> Verify that the definitional equalities are valid. Generalize
> $\UniqProd{A}{B}$ to $\Sigma$-types, and do the same for $\Sigma$-types.
> *(This requires concepts from Chapter 2.)*

* * *
The obvious way to define

$$\IndProd{A}{B}: \prod_{C : A \times B \rto \UV}
\left(\ProdTypeV{x}{A}{\ProdTypeV{y}{B}{C((\ov{x},\ov{y}))}}\right) \rto \PiType{A
\times B}{C}$$
would be to put

$$\IndProd{A}{B} \jdef
\labst{\ov{C}}{\labst{\ov{g}}{\labst{\ov{x}}{\ov{g}(\pr_1(\ov{x}),
\pr_2(\ov{x}))}}}.$$
However, this isn't well-typed, as we have

$$\ov{g}(\pr_1(\ov{x}), \pr_2(\ov{x})) : C((\pr_1(\ov{x}), \pr_2(\ov{x})))$$
and without the *judgemental* uniqueness $\ov{x} \equiv
(\pr_1(\ov{x}),\pr_2(\ov{x}))$ cannot derive the desired typing judgement
$$\ov{g}(\pr_1(\ov{x}), \pr_2(\ov{x})) : C(\ov{x}).$$
Given only *propositional* uniqueness

$$\UniqProd{A}{B}: \ProdTypeV{x}{A\times B}{((\pr_1(\ov{x}), \pr_2(\ov{x}))
=_{A\times B} \ov{x})},$$
the type needs to be changed explicitly in the definition of
$\IndProd{A}{B}$.

There are several ways to do this, all of which involve path induction^[It
isn't actually possible to define the induction principle using *only*
projections and propositional uniqueness; in this sense, the exercise is stated
incorrectly.]. The most intuitive way is to use *transport*^[The
"concept(s) from Chapter 2" alluded to in the statement of the exercise.]

$$\tp^C(\UniqProd{A}{B}(\ov{x}), \--) : C((\pr_1(\ov{x}), \pr_2(\ov{x}))) \rto
C(\ov{x}),$$

putting

$$\IndProd{A}{B} \jdef
\labst{\ov{C}}{\labst{\ov{g}}{\labst{\ov{x}}{\tp^C(\UniqProd{A}{B}(\ov{x}) , \ov{g}(\pr_1(\ov{x}),
\pr_2(\ov{x})))}}}.$$
However, I won't do this, because you can also define it using simple *based* path
induction, hence staying in the realm of the material developed in chapter one.

So instead, we put

$$\IndProd{A}{B} \jdef
\labst{\ov{C}}{\labst{\ov{g}}{\labst{\ov{x}}{\ind'_{A\times B}(\hat{a},
\widehat{C}, \hat{c}, \ov{x}, \UniqProd{A}{B}(\ov{x}))}}},$$

where we have abbreviated

\begin{align*}
\hat{a} & \equiv (\pr_1(\ov{x}), \pr_2(\ov{x})) \\
\widehat{C} & \equiv \labst{\ov{y}}{\labst{\ov{p}}{\ov{C}(\ov{y})}} \\
\hat{c} & \equiv \ov{g}(\pr_1(\ov{x}), \pr_2(\ov{x})).
\end{align*}
Of course you have to check that this is well-typed^[or rather, you'd want your
type checker to check that]. The only thing of interest here is to note that
$$\hat{c} : \widehat{C}(\hat{a},\refl_{\hat{a}})$$
as required by the principle of based path induction.

Let us now verify the "defining" equation

$$\IndProd{A}{B}(C,g,(a,b)) \equiv g(a)(b).$$
We proceed by "formal calculation" as before.

\begin{align*}
\IndProd{A}{B}(C,g,(a,b)) & \equiv
\left(\labst{\ov{C}}{\labst{\ov{g}}{\labst{\ov{x}}{\ind'_{A\times B}(\hat{a},\widehat{C},\hat{c},\ov{x},\UniqProd{A}{B}(\ov{x}))}}}\right)(C)(g)((a,b)) && \text{def.} \\
& \equiv \ind'_{A\times B}((\pr_1((a,b)), \pr_2((a,b))), \labst{\ov{y}}{\labst{\ov{p}}{C(\ov{y})}}, && \text{$\beta$-red.} \\
& g(\pr_1((a,b)), \pr_2((a,b))), (a,b), \UniqProd{A}{B}((a,b))) && \\
& \equiv \ind'_{A\times B}((\pr_1((a,b)), \pr_2((a,b))), \labst{\ov{y}}{\labst{\ov{p}}{C(\ov{y})}}, && \text{comp. rule} \\
& g(\pr_1((a,b)), \pr_2((a,b))), (a,b), \refl_{(a,b)}) && \text{for
$\UniqProd{A}{B}$} \\
& \equiv g(\pr_1((a,b)), \pr_2((a,b))) && \text{comp. rule for $\ind'$} \\
& \equiv g(a,b) && \text{comp. rule for $\pr$}
\end{align*}

Let's now generalize all this to $\Sigma$-types (a.k.a. *dependent* products).
The propositional uniqueness, which we assume to be given, is taken to be of
type

$$\uniq_{\SigmaType{A}{B}} : \prod_{\ov{p}:\SigmaType{A}{B}}
((\pr_1(\ov{p}),\pr_2(\ov{p})) =_{\SigmaType{A}{B}} \ov{p}).$$

The induction "principle" for $\Sigma$-types
$$\IndDProd{A}{B}: \prod_{C : \left(\SigmaType{A}{B}\right) \rto \UV}
\left(\prod_{\ov{a}:A} \prod_{\ov{b}:B(\ov{a})} C((\ov{a},\ov{b}))\right) \rto
\PiTypeV{p}{\SigmaType{A}{B}}{C}$$

can then be defined by the exact same formula as before

$$\IndDProd{A}{B} \jdef
\labst{\ov{C}}{\labst{\ov{g}}{\labst{\ov{x}}{\ind'_{A\times B}(\hat{a},
\widehat{C}, \hat{c}, \ov{x}, \UniqDProd{A}{B}(\ov{x}))}}},$$

where again

\begin{align*}
\hat{a} & \equiv (\pr_1(\ov{x}), \pr_2(\ov{x})) \\
\widehat{C} & \equiv \labst{\ov{y}}{\labst{\ov{p}}{\ov{C}(\ov{y})}} \\
\hat{c} & \equiv \ov{g}(\pr_1(\ov{x}), \pr_2(\ov{x})).
\end{align*}

The verification of the definitional equality/computation rule is also the
same, so no need to repeat it here.

## Exercise 1.4
> Assuming as given only the *iterator* for natural numbers
> $$\iter: \prod_{C:\UV} C \rto (C \rto C) \rto \N \rto C$$
> with the defining equations
> \begin{align*}
> \iter(C,c_0,c_s,0) & \jdef c_0, \\
> \iter(C,c_0,c_s,\suc(n)) & \jdef c_s(\iter(C, c_0, c_s, n)),
> \end{align*}
> derive a function having the type of the recursor $\rec_{\N}$. Show that the
> defining equations of the recursor hold propositionally for this function,
> using the induction principle for $\N$.

* * *
Recall that
$$\rec_{\N}: \prod_{C:\UV} C \rto (\N \rto C \rto C) \rto \N \rto C$$
with
\begin{align*}
   \rec_{\N}(C,c_0,c_s,0) & \equiv c_0 \\
   \rec_{\N}(C,c_0,c_s,\suc(n)) & \equiv c_s(n, \rec_{\N}(C,c_0,c_s,n)).
\end{align*}

The obvious idea of how to derive the recursor from the iterator is to replace
$C$ by the product type $\N \times C$ and replace the "recursion function"
$c_s$ by the "iteration function" $(n,c) \mapsto (\suc(n),c_s(n,c))$.

Thus, we define the sought-after function $r$ by

$$r(C,c_0,c_s,n) \jdef \pr_2(\iter(\N \times C, (0, c_0),
\labst{\ov{n}}{\labst{\ov{c}}{(\suc(\ov{n}), c_s(\ov{n}, \ov{c}))}}), n)).$$

Intuitively, it seems clear that we should get the recursor equations for the function $r$, just
by "looking" at this expression. However, this intuition is based on
manipulating functions in set theory, and in particular doesn't account for the
fact that lambda forms have no reason to respect judgemental equalities (we
only require *congruence* for constructors and eliminators).

Therefore, we can only show that these equations hold *propositionally*.
Indeed, abbreviating

$$f \jdef \labst{\ov{n}}{\labst{\ov{c}}{(\suc(\ov{n}), c_s(\ov{n},\ov{c}))}},$$
we can calculate

\begin{align*}
r(C,c_0,c_s,\suc(n)) & \equiv \pr_2(\iter(\N \times C, (0, c_0), f, \suc(n))) \\
& \equiv \pr_2(f(\iter(\N \times C, (0, c_0), f, n)))
\end{align*}
judgementally, but then cannot proceed any further for two reasons.

First, we cannot derive the equation

$$\iter(\N \times C, (0, c_0), f, n) \equiv (n, \pr_2(\iter(\N \times C, (0, c_0), f, n)))$$
because we cannot *judgementally* conclude that
$$\pr_1(\iter(\N \times C, (0, c_0), f, n) \equiv n.$$

Second, even if we could, this equation wouldn't need to be respected by $f$.

So, let us fix this by first deriving a propositional version of the equation
above, i.e. let us find a term of type

$$D(n) \jdef \pr_1(\iter(\N \times C, (0,c_0), f,n) =_{\N} n$$
under the context^[In the following (and probably thereafter), we will relax
our convention of denoting object language terms using \texttt{typewriter
font}, when it seems harmless; in particular, $C$, $c_0$, $c_s$ and $n$ denote
object variables in the following.]
$$\underbrace{C : \UV, c_0 : C, c_s : \N \rto C \rto C}_{\Gamma}, n : \N.$$
We do this by induction. First

\begin{align*}
\text{(1)} && \Gamma \vdash \iter(\N \times C, (0,c_0), f, 0) \equiv (0,c) & : \N\times C && \\
\text{(2)} && \Gamma \vdash \pr_1(\iter(\N \times C, (0, c_0), f, 0)) \equiv \pr_1((0,c))
& : \N && \text{(1), congruence} \\
\text{(3)} && \Gamma \vdash \pr_1((0,c)) \equiv 0 & : \N && \text{comp. rule}
\\
\text{(4)} && \Gamma \vdash \pr_1(\iter(\N \times C, (0, c_0), f, 0)) \equiv
0 & : \N && \text{(2), (3), $\equiv$-trans.} \\
\text{(5)} && \Gamma \vdash \refl_0 & : D(0) && \text{$=$-INTRO
+ $\text{Subst}_2$ + (4)}.
\end{align*}

Second, abbreviating
$$g(n) \jdef \iter(\N \times C, (0, c_0), f, n),$$
we have

\begin{align*}
   \text{(1)} && \Gamma, n : \N \vdash g(\suc(n))
   \equiv f(g(n)) : \N \times C && \text{by assumption} \\
   \text{(2)} && \Gamma, n : \N \vdash \UniqProd{\N}{C}(g(n)) : (\pr_1(g(n)), \pr_2(g(n))) =_{\N\times C} g(n) && \\
   \text{(3)} && \Gamma, n : \N, d : D(n) \vdash d : \pr_1(g(n)) =_{\N} n &&
   \text{Vble} \\
   \text{(4)} && \Gamma, n : \N, d : D(n) \vdash \mathfrak{m}(d)
   : (n,\pr_2(g(n))) =_{\N\times C} (\pr_1(g(n)), \pr_2(g(n))) && \text{by
   magic} \\
   \text{(5)} && \Gamma, n : \N, d : D(n) \vdash \mathfrak{m}(d)\ct
   \UniqProd{\N}{C}(g(n)) : (n, \pr_2(g(n))) =_{\N \times C} g(n) &&
   \text{(2),(4)} \\
   \text{(6)} && \Gamma, n : \N, d : D(n) \vdash \ap_{f}(\mathfrak{m}\ct
   \UniqProd{\N}{C}(g(n))) : f((n,\pr_2(g(n)))) =_{\N\times C} f(g(n)) &&
   \text{(5)}. \\
   \intertext{Putting
   $$h(n,d) \jdef (\mathfrak{m}(d)\ct \UniqProd{\N}{C}(g(n)))^{-1},$$
   we therefore have}
   \text{(6)} && \Gamma, n : \N, d : D(n) \vdash h(n,d) : g(n) =_{\N\times C}
   (n,\pr_2(g(n))) && \text{by (5).} 
   \end{align*}
   From this we can derive two things. First, we get
   \begin{align*}
   \text{(7)} && \Gamma, n : \N \vdash g(\suc(n)) \equiv f(g(n)) && 
   \text{by def.} \\
   \text{(8)} && \Gamma, n : \N, d : D(n) \vdash \ap_f(h(n,d)) : f(g(n)) =_{\N
   \times C} f((n, \pr_2(g(n)))) && \text{(6)} \\
   \text{(9)} && \Gamma, n : \N, d : D(n) \vdash \ap_f(h(n,d)) : g(\suc(n)) =_{\N
   \times C} f((n, \pr_2(g(n)))) && \text{(7),(8)} \\
   \text{(10)} && \Gamma, n : \N \vdash f((n, \pr_2(g(n)))) \equiv (\suc(n),c_s(n,\pr_2(g(n)))) : \N \times C && \text{def. + $\beta$-red.} \\
   \text{(11)} && \Gamma, n : \N, d : D(n) \vdash \ap_f(h(n,d)) : g(\suc(n)) =_{\N
   \times C} (\suc(n),c_s(n, \pr_2(g(n)))) && \text{(9),(10)} \\
   \text{(12)} && \Gamma, n : \N, d : D(n) \vdash \ap_{\pr_1}(\ap_f(h(n,d)))
   : D(\suc(n)) && \text{(11)}. \\
   \intertext{Thus we can use induction to populate $D(n)$ for all $n$}
   \text{(13)} && \Gamma, n : \N \vdash \underbrace{\ind_{\N}(\refl_0,
   \labst{n}{\labst{d}{\ap_{\pr_1}(\ap_f(h(n,d)))}}, n)}_{\equiv: d(n)} : D(n), && \\
   \intertext{and hence eliminate the variable $d : D(n)$ from our context}
   \text{(14)} && \Gamma, n : \N \vdash \ap_f(h(n, d(n))) : g(\suc(n))
   =_{\N\times C} (\suc(n), c_s(\pr_2(g(n)))) && \text{(11),(13)}
\end{align*}
