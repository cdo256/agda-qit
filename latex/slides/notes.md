# Outline

# Overview

- Simplicial maps
- Develop one of the simplest 'interesting' examples of a traced monoidal category.

# Methodology

The aim of this project was to construct a certain mathematical
structure dubbed a 'virtual set' within Agda, a proof assistant. The
project amounted to ~4.5k lines of Agda consisting of 340 top level
definitions, building up from properties about finite sets to all of
the constructions within this project.

Not all lemmas were proved in the end as the project appeared to be
much more involved than expected. Further work could reinforce these
gaps.

# Problem statement

- Injectivity of a mathematical function just means that no two
  distinct inputs can result in the same output.
- Start with injective functions on finite sets. 
- We can form a tensor by joining the domain and codomain.
- We define a predecessor operator which can be visualised by drawing a loop and pulling.
- then we conjecture that:
  - The set of injective functions on finite sets forms a 'category'
  - There is a certain tensor product.
  - That tensor product satisfies the monoidal element

# Definition of Inj

\begin{tikzpicture}[thickedge, node distance=7mm]
  \dotrow{2}{b}{above}
  \begin{scope}[yshift=-2cm]
    \dotrow{2}{a}{below}
  \end{scope}
  \draw (a0) -- (b1);
  \draw (a1) -- (b2);
  \draw (a2) -- (b0);
 \draw[thick,->,>=stealth, line width=2pt] (3,-2) -- ++(0,2);
\end{tikzpicture}

One of the main components is a convenient definition of Inj, 
we use an inductive definition where we either have the empty map
`nul` or we construct the map by adding a link to some other injective
map, shifting values to preserve injectivity. This definition was
picked mid-way through the
project due to the difficulty working with dependent pairs,
specifically working with the proof of injectivity.

```
data Inj : ℕ → ℕ → Type where
  nul : 0 ↣ n
  inc : (b : Fin (suc n))
      → (f: m ↣ n)
      → (suc m) ↣ (suc n)
```

We use ↣ as the symbol for injective functions.

# Tensor Operation

\begin{tikzpicture}[thickedge, node distance=7mm]
  \dotrow{6}{b}{above}
  \begin{scope}[xshift={(-5, -2)}]
    \dotrow{2}{a}{below}
  \end{scope}
  \begin{scope}[xshift={(-5, -2)}]
    \dotrow{3}{a}{below}
  \end{scope}
  \draw (a0) -- (b1);
  \draw (a1) -- (b2);
  \draw (a2) -- (b0);
 \draw[thick,->,>=stealth, line width=2pt] (3,-2) -- ++(0,2);
\end{tikzpicture}
