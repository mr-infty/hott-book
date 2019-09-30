# Typographical Conventions

* Object-language terms are written in \texttt{fixed-width}^[However, strings in
  fixed-width font beginning with a question mark like $\ttt{?f}$ do *not* denote object language terms but "holes"; see below.] or special fonts
  (e.g. $\N$, $\mathcal{U}_0$), whereas meta-language terms are written in `normal',
  variable-width font. For example, in the sentence

  $$\text{If $A,B : \mathcal{U}_0$ and $f : A \rightarrow B$, then $f \equiv \lambda \texttt{x}.\
  f(\texttt{x})$}.$$

  the symbols '$t$', '$A$' and '$B$' denote meta-variables denoting arbitrary for object-language
  terms, whereas the symbols '$\mathcal{U}_0$' and '$\texttt{x}$' denote object-language terms.

* When the context $\Gamma$ of a sequent

  $$\Gamma \vdash J$$

  is empty, we may drop the turnstile and simply denote it by $J$. Or, we might
  write it as
  $$\vdash J$$
  or even use the book's convention and denote the empty context explicitly
  using a dot
  $$\emptyctx \vdash J.$$

* When presenting deduction rules, we will usually drop the parentheses in
  contexts, e.g. we write

  $$\inferrule{a : A \\ b : B \\ x : A, y : B \vdash f(x,y) : C}{a : A,
  b : B \vdash f(a,b) : C}$$

  instead of

  $$\inferrule{a : A \\ b : B \\ (x : A, y : B) \vdash f(x,y) : C}{(a : A,
  b : B) \vdash f(a,b) : C}.$$

  In accordance with this convention, *concatenation of contexts* will be
  denoted using a *comma*.

  For example, if
  
  $$\Gamma = (x : X, y : Y)\quad \text{and}\quad \Gamma' = (a : A, b : B),$$
  then $\Gamma, \Gamma'$ denotes
  
  $$(x : X, y : Y, a : A, b : B).$$
  Similarly, $\Gamma, z : Z$ denotes $(x : X, y : Y, z : Z)$.

* *Holes* are indicated using the symbol $\Box$, as in
   \begin{align*}
   \text{(0)} && \Gamma \vdash \labstt{x}{A}{\Box} : \prod_{x : A} B &&
   \text{(-1), $\Pi$-INTRO} \\
   \text{(-1)} && \Gamma, x : A \vdash \Box : B. &&
   \end{align*}
   Named holes are indicated by a question mark followed by a meta-variable name, all written in fixed-width font, as in
   \begin{align*}
   \text{(0)} && \Gamma \vdash \labstt{x}{A}{\ttt{?f}} : \prod_{x : A} B &&
   \text{(-1), $\Pi$-INTRO} \\
   \text{(-1)} && \Gamma, x : A \vdash \ttt{?f} : B. &&
   \end{align*}

* If $f$ is a function symbol that's usually written in infix notation, we will
  write $(f)$ (following the Idris convention) when we want to indicate that it is written in postfix.
  
  For example, we might write
  $$\labstt{\N}{n}{\labstt{\N}{m}{n+m}}$$
  also as
  $$\labstt{\N}{n}{\labstt{\N}{m}{(+)(n,m).}}$$

# On holes

The concept of a "hole" is crucial for the practicality of programming in
depenently typed programming languages; for that same reason, we must
talk about it here, since there is no difference between that activity and
doing proofs in type theory.

## The problem 

If life would be easy^[Newsflash, it's not.], whenever we'd want to prove something in type theory,
i.e. find a term $t$ of a given type $T$, we would just come up with
a (linearized) derivation tree ending in the desired judgement
$$\Gamma \vdash t : T.$$
However, unless this derivation is obvious, proving things in the "forward"
direction is unnatural; instead, it is usually easier to prove things
"backwards", by reducing the "goal" $\Gamma \vdash t : T$ to simpler subgoals. 

For example, if $T \equiv \prod_{x : A} B(x)$, it would be natural to make an ansatz of the form $t
   \equiv \labst{x}{f}$, reducing the goal to $\Gamma, x : A \vdash f : B(x)$.

That's pretty obvious. However, a small problem arises if we are to write down
such a "backwards" proof formally because a formal^[Our "formal proofs" aren't really
formal, because we leave out intermediate, "obvious" steps in the
linearized derivation tree.] proof *ends* with the goal, hence we need to know
the complete proof in advance before the goal can even be written down.

Thus it becomes natural to write down the derivation tree in reverse order,
beginning with the end goal. However, that still doesn't solve the problem,
since the term $t$ isn't known in advance, even given the ansatz $t \equiv
\labst{x}{f}$, since $f$ is a *meta-variable* standing for
a *yet-to-be-determined term*.

## The solution

The solution is to simply leave this meta-variable uninstantiated, i.e. to
leave a **hole** in derivation tree, which is to be filled in later.

This "hole" will be denoted by the symbol $\Box$. Thus, the beginning of our
backwards linearized derivation tree could look as follows:

\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{\Box} : \prod_{x : A} B &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash \Box : B. &&
\end{align*}
The way the hole $f$ arises in the above application of $\Pi-\text{INTRO}$ is
exemplary of the general case:

> *holes are introduced by applying a derivation
> rule (scheme) containing a meta-variable ranging over terms but without
> supplying an actual term for one (or more) of those meta-variables.*

In the rule (scheme)
$$\inferrule*[right=\text{$\Pi$-INTRO}]{\Gamma, x : A \vdash b : B}{\Gamma \vdash
\labstt{x}{A}{b} : \prod_{x : A} B},$$
there are three^[To be really precise, $x$ is also a meta-variable, ranging
only over object variables and not arbitrary terms however.] meta-variables: $A,B$ and $b$; but, since $T \equiv \prod_{x
: A} B$ determines $A$ and $B$ uniquely^[perhaps up to judgemental equality] (given $T$), it effectively only contains one meta-variable for our purposes.

The relation between the two "holes" in the judgements^[Since they contain
meta-variables/holes, they aren't judgements, strictly speaking.]
\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{\Box} : \prod_{x : A} B &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash \Box : B. &&
\end{align*}
is already fixed by specifying that the rule scheme $\Pi$-INTRO is used to
derive (0) from (-1): the contents of the (unique) box in judgement (-1) are to be placed inside the (unique) box in judgement (0), once the former box is filled.

However, sometimes (especially when applying a rule scheme containing several
meta-variables) it's helpful to make this relation more explicit by naming the
holes, i.e. by inserting an actual meta-variable instead of the box symbol.
Following a popular convention from dependently typed programming, these
meta-variables will be written in fixed-width font with a question mark infront, to clearly
mark them as such.

The example above could therefore have also been written as

\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{\ttt{?f}} : \prod_{x : A} B &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash \ttt{?f} : B. &&
\end{align*}

## Filling holes

Once a hole has been created in a proof, you must eventually *fill* it in order
to obtain a complete derivation. To fill a hole means to have
a complete^[complete up to *filled* holes] derivation ending^[i.e. starting in
it, if the derivation is written backwards] in it.

For instance, if in the above example we had $A \equiv B$, we could fill the
hole as follows:

\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{\ttt{?f}} : \prod_{x : A} A &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash \ttt{?f} : A. && \text{(-2),Vble} \\
\text{(-2)} && \Gamma, x : A\ \ctx && \text{by assumption.}
\end{align*}
Again, that the term $x$ is to be inserted into the hole $\ttt{?f}$ is implicit
in stating that rule $\text{Vble}$ is used to derive (-1) from (-2).

## Removing holes

Once all holes in a derivation with holes are "filled", we can derive
a "normal" derivation (without holes), by substituting the filling terms into
their corresponding holes, successively from bottom to top.

For example, removing the holes in the above three-step derivation results in

\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{x} : \prod_{x : A} A &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash x : A. && \text{(-2),Vble} \\
\text{(-2)} && \Gamma, x : A\ \ctx && \text{by assumption.}
\end{align*}

Since this is a completely mechanical operation that is
obviously\texttrademark{} well-defined and correct,
there is no need to actually carry it out. So, we won't.

## Updating

Even though writing derivations backwards and using holes help in reconciling
the *interactive* nature of dependently typed programming with the *linear* and 
*immutable* nature of written text, some tension remains.

It is therefore sometimes convenient to "update" a judgement, i.e. to first
write down a preliminary version (e.g. in order to have something 
that can be referred to verbally) and then afterwards follow
it by a more complete, or final version.

We adopt the convention that *a judgement always supersedes any previous ones
with the same number*. Here we mean by "supersede" that a newer version
replaces an older one *in situ*, i.e. even if more judgements (with lower
numbers) are written down in between, judgements are to be read in order
according to their numbering.

For instance, in the example below we want to derive the addition on natural
numbers, so we might want to start by writing down
\begin{align*}
\text{(0)} && \vdash (\ttt{?+}) : \N \rto \N \rto \N && 
\end{align*}
in order to fix the type of the sought-after term in the readers mind. Then, we
might want to bring to the readers attention the convention regarding
associativity of the arrow notation and rewrite the judgement as
\begin{align*}
\text{(0)} && \vdash (\ttt{?+}) : \N \rto (\N \rto \N), && 
\end{align*}
so that it immediately suggests the application of the induction principle,
which then leads us to rewrite it a second (and final) time as
\begin{align*}
\text{(0)} && \vdash (\ttt{?+}) : \N \rto (\N \rto \N) && \text{$\N$-ELIM on
(-1),(-2)} \\
\text{(-1)} && \vdash \ttt{?add}_0 : \N \rto \N && \\
\text{(-2)} && n : \N, f : \N \rto \N \vdash \ttt{?add}_s(n,f) : \N \rto \N. &&
\end{align*}
Once again, stating that (0) is derived from (-1) and (-2) contains some
implicit information, in this case the assumed judgemental equality
$$(\ttt{?+}) \equiv \ind_\N(\labst{n}{\N \rto \N}, \ttt{?add}_0, \ttt{?add}_s).$$ 
If we want to make this explicit (which in this case we probably would), we
could have done so by writing
\begin{align*}
\text{(0)} && \vdash \ind_\N(\labst{n}{\N \rto \N}, \ttt{?add}_0, \ttt{?add}_s) : \N \rto (\N \rto \N) && \text{$\N$-ELIM on (-1),(-2)}
\end{align*}
instead (or even afterwards).

## Example of a derivation containing holes

To fix ideas, let us look at a more complicated derivation, containing several
holes.

First, let us define addition of natural numbers
\begin{align*}
\text{(0)} && \vdash (\ttt{?+}) : \N \rto \N \rto \N. && \\
\intertext{Recalling that $\rto$ associates to the right}
\text{(0)} && \vdash (\ttt{?+}) : \N \rto (\N \rto \N), && \\
\intertext{it's natural to try to use induction to fulfill this
goal:}
\text{(0)} && \vdash \ind_\N(\labst{n}{\N \rto \N}, \ttt{?add}_0, \ttt{?add}_s) : \N \rto (\N \rto \N) && \text{$\N$-ELIM on (-1),(-2)} \\
\text{(-1)} && \vdash \ttt{?add}_0 : \N \rto \N && \\
\text{(-2)} && n : \N, f : \N \rto \N \vdash \ttt{?add}_s(n,f) : \N \rto \N. && \\
\intertext{Addition should satisfy $0 + m \equiv m$ and $(\suc(n))+ m \equiv \suc (n+m)$, so we plug those holes as follows.}
\text{(-1)} && \vdash \labstt{\N}{m}{m} : \N \rto \N && \text{obviously} \\
\text{(-2)} && n : \N, f : \N \rto \N \vdash \labstt{\N}{m}{\suc(f(m))} : \N \rto \N && \text{obviously}
\end{align*}
Thus, addition is given by the following term of inarguable, majestic beauty:
$$(+) \equiv \ind_\N(\labst{n}{\N \rto \N}, \labst{m}{m}, \labst{n}{\labst{f}{\labst{m}{\suc(f(m))}}}.$$

Second, let's prove that addition is associative.
So we want to inhabit
\begin{align*}
\text{(0)} && n,m,k : \N \vdash \Box : (n+m) + k =_\N n + (m + k). && \\
\intertext{Of course we are going to use induction for this, so we somehow need
to get a function $\N \rto$ in there. Since we want to use induction on the
variable $n$, we produce this function by lambda abstracting on that variable:}
\text{(0)} && n,m,k : \N \vdash \ttt{?f}(n) : (n+m) + k =_\N n + (m + k) && \text{$\Pi$-ELIM on (-1)} \\
\text{(-1)} && m,k : \N \vdash \ttt{?f} : \prod_{n : \N} (n+m) + k =_\N n + (m + k). && \\
\intertext{Now we plug this hole using induction:}
\text{(-1)} && m,k : \N \vdash \ttt{?f} : \prod_{n : \N} (n+m) + k =_\N n + (m + k) && \text{$\N$-ELIM on (-2), (-3)} \\
\text{(-2)} && m,k : \N \vdash \ttt{?f}_0 : (0+m) + k =_\N 0 + (m + k) && \\
\text{(-3)} && m,k : \N, n : \N, p : (n+m) + k =_\N n + (m + k) && \\
&& \vdash \ttt{?f}_s(n,p) : (\suc(n)+m) + k =_\N \suc(n) + (m + k). && \\
\intertext{Now by construction of $(+)$, we have $$0 + m \equiv m$$
\textit{judgementally} (by $\N\text{-COMP}_1$). Therefore, we can easily plug $\ttt{?f}_0$:}
\text{(-2)} && m,k : \N \vdash \refl_{m+k} : (0+m) + k =_\N 0 + (m + k). && \\
\intertext{By $\N\text{-COMP}_2$, we have
$$\suc(n)+ \_ \equiv \ttt{add}_s(n,n+\_) \equiv \labst{m}{\suc(n+m)}.$$
Thus $\suc(n)+m \equiv \suc(n+m)$ by $\beta$-reduction. We can therefore
rewrite (-3) equivalently as}
\text{(-3)} && m,k : \N, n : \N, p : (n+m) + k =_\N n + (m + k) && \\
&& \vdash \ttt{?f}_s(n,p) : \suc((n+m) + k) =_\N \suc(n + (m + k)). && \\
\intertext{Now it's obvious how to plug $?\ttt{f}_s$, we simply use
(non-dependent) ``action on paths'':}
\text{(-3)} && m,k : \N, n : \N, p : (n+m) + k =_\N n + (m + k) && \\
&& \vdash \ap_{\labst{x}{\suc(x)}}(p) : \suc((n+m) + k) =_\N \suc(n + (m + k)). && \\
\end{align*}
