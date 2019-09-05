---
toc: true
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
preferrably on a computer, rather than merely asserting that that's possible.],
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

Let us now prove the judgemental associativity

$$h \circ (g \circ f) \equiv (h \circ g) \circ f,$$

or rather,

$$\labstt{\ttt{x}}{A}{h(\labstt{\ttt{x}}{A}{g(f(\ttt{x}))}(\ttt{x}))} \equiv \labstt{\ttt{x}}{A}{(\labstt{\ttt{x}}{A}{h(g(\ttt{x})))(f(\ttt{x}))}}.$$

We will do this by rewriting both sides of the equation (one side at a time),
meaning that in each step we replace a subterm---indicated by underlining---with
another one that can be proved to be judgementally equal to it via one of the
rules of appendix A.2. The rule being used will be indicated above the
$\equiv$-sign.

Note that replacing a subterm by something that's judgementally
equal to it results in a term that's still judgementally equal to the original
term; this follows from the rule $\text{Subst}_2$ in A.2.2.

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

using the projections

\begin{align*}
\pr_1 & : A \times B \rto A \\
\pr_2 & : A \times B \rto B
\end{align*}

as

$$\rec_{A\times B}(C, g, p) \jdef g(\pr_1(p), \pr_2(p)).$$
