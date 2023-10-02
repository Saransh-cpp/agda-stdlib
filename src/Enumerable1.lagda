Finitary and Enumerable containers.
\begin{code}

{-# OPTIONS --without-K --safe #-}

module Data.Container.Enumerable where
  open import Data.Container.Core using (Container ; Shape ; ⟦_⟧; Position) renaming (map to mapC)
  open import Data.Fin using (Fin)
  open import Data.Nat using (ℕ; _>_)
  open import Data.Product using (Σ ; _,_)
  open import Level using (Level; _⊔_)
  open import Function using (Injective; _↔_; _∘_; id)
  open import Relation.Unary using (Pred)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
  open import Function.Bundles using (Inverse; mk↔′)

  open import Data.Container.Utils using (shape; get)
\end{code}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  Enumerable Types and Structures

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%<*isenumdef>
Thus, we say that a \Type \ is enumerable if we can exhibit an isomorphism
between that type and \Fin \ \nT \ for some \nT.
\begin{code}
  record IsEnumerable {x : Level} (X : Set x) : Set x where 
    constructor sz_en_#
    field
      size : ℕ
      enum : Fin size ↔ X
\end{code}
\size \ ensures that we will have a finite enumeration between the type and the numbers.
Moreover, \enum \ encodes the bi-directional relation between finite numbers and members
of the type. The bi-directional arrow ↔ is defined in the standard library as having two
functions \AgdaFunction{f} and \AgdaFunction{f$^{-1}$} which are inverses of each other.
\AgdaFunction{f} converts a \Fin \ \nT \ to a value of type \XT. While \AgdaFunction{f$^{-1}$}
satisfies the opposite translation. These functions are total, where the cardinality of 
the range and domain is \size.
%</isenumdef>

\begin{code}
  module _ {s p : Level} (C : Container s p) where
\end{code}

%<*enumstructdef>

\IsEnum \ is defined for \emph{any} \Type. Hence, we need a definition that will
work on structures such that we can perform any folds on them.
We define an \Enumerable \ (structure) which states that a
\Shape \ is enumerable if its associated set of \Position s is enumerable.
\begin{code}
    Enumerable : Pred (Shape C) p
    Enumerable S = IsEnumerable (Position C S)
\end{code}
%</enumstructdef>

\begin{code}
  module Structure {s p : Level} {C : Container s p} (S : Shape C) (e : Enumerable C S) where
    open Inverse
    open IsEnumerable e
    private
      variable
        a : Level
        A : Set a
\end{code}

%<*enumstructfunctions>
An enumerable structure \AgdaArgument{e} can be both indexed and tabulated,
much like Naperian functors\footnote{See section \ref{sec:extra:naperian} for a discussion 
about naperian.}\citep{gibbons2016} (and representable functors).
This is because locally enumerable fixes the shape (or the log).
However, the converse is not true.
With \AgdaFunction{index}, we can use \Fin \ to retrieve the piece of
data stored at that number. \AgdaFunction{tabulate} recreates the original
structure. We cannot change the shape that we have, but we know that
since a set of positions is enumerable, then given a value for each position,
we can retrieve the value by mapping the positions to values. In turn, we
fill the ``holes''. Finally, we define \positions, a function which returns 
the \Position \ associated to the unique number.

\begin{code}
    index : (Position C S → A) → Fin size → A
    index get fn =  get (f enum fn)

    tabulate : (Fin size → A) → ⟦ C ⟧ A
    tabulate g = S ,  g ∘ f⁻¹ enum

    positions : Fin size → Position C S
    positions fn = f enum fn
\end{code}
%</enumstructfunctions>

%<*coherentlyenum>
\todo{this might just go in extra}
For some of the more interesting notions of enumerability (like indexed sums), we need an
extra notion of \emph{coherently enumerable} where the proofs of invertibility are
related.
\begin{code}
  record IsCoherentlyEnumerable {x : Level} (X : Set x) : Set x where
    field
      isEnumerable : IsEnumerable X
    open IsEnumerable isEnumerable
    open Inverse enum
    field
      coh : ∀ j → ≡.cong f⁻¹ (inverseˡ j) ≡ inverseʳ (f⁻¹ j)
\end{code}
%</coherentlyenum>

%<*inhabited>
Lastly, a shape is inhabited exactly when its size is strictly positive.
In other words, the structure must not be empty.
\begin{code}
  module _ {s p : Level} (C : Container s p) where
    Inhabited : Pred (Shape C) p
    Inhabited S = Σ (Enumerable C S) (λ e → IsEnumerable.size e > 0)
\end{code}
%</inhabited>

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

  Finitary and Enumerable Containers

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{code}
  module _ {s p a : Level} {C : Container s p} {A : Set a} (T : ⟦ C ⟧ A) where
\end{code}
%<*finitarydef>
We begin by defining a notion of a \Finitary \ structure which ensures that
the structure is finite \emph{and} gives an injective map from a \Position \ to 
a \Fin \ \nT.
\begin{code}
    Finitary : Set p
    Finitary = Σ ℕ (λ n → Σ (Position C (shape T) → Fin n) 
               (λ f → Injective _≡_ _≡_ f))
\end{code}
However, this is rather weak, as it only give an upper bound on the size. Moreover, while
this provides a unique number for each \Position, figuring out how to accumulate a structure 
would be impossible, as there is no function between \Fin \ and the value of the structure.
%</finitarydef>


%<*enumerablecdef>
A \Container \ is enumerable if for all its \Shape s, the positions
are enumerable. In this way, we have a stronger definition as we have an
isomorphism between the positions of a container, and \Fin \ \nT.
\begin{code}
  module _ {s p : Level} where
    EnumerableC : Pred (Container s p) (s ⊔ p)
    EnumerableC C = ∀ (S : Shape C) → IsEnumerable (Position C S)
\end{code}
%</enumerablecdef>

%<*enumerablecfunctions>
We are even able to define \AgdaFunction{index}, \AgdaFunction{tabulate},and
\AgdaFunction{positions} for \EnumerableC \ quite easily.
\begin{code}
  module Cont {s p a : Level} {C : Container s p} {A : Set a} (T : ⟦ C ⟧ A) (E : EnumerableC C) where
    open Inverse
    open IsEnumerable (E (shape T))

    index : Fin size → A
    index fn =  get T (f enum fn)

    tabulate : (Fin size → A) → ⟦ C ⟧ A
    tabulate g = shape T ,  g ∘ f⁻¹ enum

    positions : Fin size → Position C (shape T)
    positions fn = f enum fn
\end{code}
%</enumerablecfunctions>

