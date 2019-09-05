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
