# Typographical Conventions

* Object-language terms are written in \texttt{fixed-width} or special fonts
  (e.g. $\N$, $\mathcal{U}_0$), whereas meta-language terms are written in `normal',
  variable-width font. For example, in the sentence

  $$\text{If $A,B : \mathcal{U}_0$ and $f : A \rightarrow B$, then $f \equiv \lambda \texttt{x}.\
  f(\texttt{x})$}.$$

  the symbols '$t$', '$A$' and '$B$' denote meta-variables denoting arbitrary for object-language
  terms, whereas the symbols '$\mathcal{U}_0$' and '$\texttt{x}$' denote object-language terms.

* When the context $\Gamma$ of a sequent

  $$\Gamma \vdash J$$

  is empty, we may drop the turnstile and simply denote it by $J$.

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
   Named holes are indicated by a question mark followed by a meta-variable name, all written in fraktur, as in
   \begin{align*}
   \text{(0)} && \Gamma \vdash \labstt{x}{A}{\mathfrak{?f}} : \prod_{x : A} B &&
   \text{(-1), $\Pi$-INTRO} \\
   \text{(-1)} && \Gamma, x : A \vdash \mathfrak{?f} : B. &&
   \end{align*}


# On "holes"

The concept of a "hole" is extremely important for the practical usefulness
of dependently typed programming languages; for that same reason, we must
talk about it here, since there is no difference between making proofs in
type theory and programming in dependently typed programming languages.

## The problem 

If life would be easy, whenever we'd want to prove something in type theory,
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
derive (0) from (-1): the contents of the (unique) box in judgement (-1)---once that boxed is filled---are to be placed inside the (unique) box in judgement (0).

However, sometimes (especially when applying a rule scheme containing several
meta-variables) it's helpful to make this relation more explicit by naming the
holes, i.e. by inserting an actual meta-variable instead of the box symbol.
Following a popular convention from dependently typed programming, these
meta-variables will be written in *fraktur*^[Unforunately, I already chose to use \ttt{typewriter font} for literal object language terms, and fonts like \ttt{mathcal} are very limited.] with a question mark infront, to clearly
mark them as such.

The example above could therefore have also been written as

\begin{align*}
\text{(0)} && \Gamma \vdash \labstt{x}{A}{\mathfrak{?f}} : \prod_{x : A} B &&
\text{(-1), $\Pi$-INTRO} \\
\text{(-1)} && \Gamma, x : A \vdash \mathfrak{?f} : B. &&
\end{align*}

## Example of a derivation containing holes

To make things clearer, let us look at a complete example derivation that uses holes.

