# Automated Reasoning — Lectures 2–7 (Claude Opus5)

## Inference Systems, Saturation, Redundancy, Equality, Term Orderings, Unification, and Superposition

*Consolidated, corrected, and completed notes.*

Source material: the Online Vampire Guide by Laura Kovács and Andrei Voronkov —
[L2](https://vprover.github.io/vampireGuide/docs/lectures/l2),
[L3](https://vprover.github.io/vampireGuide/docs/lectures/l3),
[L4](https://vprover.github.io/vampireGuide/docs/lectures/l4),
[L5](https://vprover.github.io/vampireGuide/docs/lectures/l5),
[L6](https://vprover.github.io/vampireGuide/docs/lectures/l6),
[L7](https://vprover.github.io/vampireGuide/docs/lectures/l7),
plus the exercise pages
[Ex-L2](https://vprover.github.io/vampireGuide/docs/exercises/ex-l2),
[Ex-L3](https://vprover.github.io/vampireGuide/docs/exercises/ex-l3),
[Ex-L4](https://vprover.github.io/vampireGuide/docs/exercises/ex-l4),
[Ex-L5](https://vprover.github.io/vampireGuide/docs/exercises/ex-l5),
[Ex-L6](https://vprover.github.io/vampireGuide/docs/exercises/ex-l6),
[Ex-L7](https://vprover.github.io/vampireGuide/docs/exercises/ex-l7).

---

## 0. How to read this document

The six lectures form one continuous story:

> **L2**: what an inference system is, binary resolution, and how *selection functions* restrict it → **L3**: how to turn "there exists a derivation" into a *search procedure* — saturation, fairness, the given-clause algorithm → **L4**: what "redundant" means and why we may delete redundant clauses → **L5**: how to order terms so that superposition is usable on ground clauses → **L6**: how to solve equations between terms (unification) so that one non-ground inference stands for infinitely many ground ones → **L7**: the full non-ground superposition calculus and the redundancy machinery a real prover runs.

Lectures 2 and 3 supply three things the later lectures use constantly but never restate: the **literal ordering**, the definition of a **well-behaved selection function**, and the **saturation/fairness** framework. Earlier versions of these notes started at L4 and consequently had to guess at all three. Those guesses are now replaced by the published definitions, and the errata that rested on them have been corrected — see §A.9 for the list of self-corrections.

Three kinds of edit have been applied to the original material:

| Marker | Meaning |
|---|---|
| *(silent)* | Plain typos, spacing, and wording fixed without comment. |
| **▸ Fixed** | A statement that was wrong or misleading as published; the corrected version is given and the change is explained. |
| **▸ Completed** | Something the original left unfinished (an example with no task, an exercise with no answer, a definition covering only some cases). |

Every one of these is also listed in **Appendix A (Errata)** so you can diff against the website.

### A note on the website's rendering

On every lecture page the `≠` symbol renders as `=` in the plain-text/copy-paste fallback of the MathML. So the page that displays

$$f(f(a)) \neq a$$

copies out as `f(f(a))=a`. If you have been reading the pages via copy-paste, screen reader, or "view source", **assume every equality you see may actually be a disequality** and check against the LaTeX in the page source. Several apparent contradictions in the lecture notes are only this rendering bug. All formulas below are written with the intended symbol.

### Contents

| | |
|---|---|
| §0–§1 | How to read this; conventions, symbols, the literal ordering |
| **L2** §2.1–§2.11 | inference systems · derivations · $\mathbb{BR}$ · soundness · **selection functions** · why selection alone breaks completeness · **well-behaved selection** · completeness of $\mathbb{BR}\sigma$ |
| **L3** §3.1–§3.12 | **saturated sets & closure** · inference process · limit · **fairness** · completeness reformulated · given-clause algorithm · active/passive · **saturation algorithm**, theory vs practice |
| **L4** §4.1–§4.17 | bag extension · clause ordering · **redundancy** · process with deletion · persistent clauses · saturation up to redundancy · equality · simple ground superposition |
| **L5** §5.1–§5.10 | equality literal ordering · $\mathbb{S}\mathrm{up}_{\succ,\sigma}$ · simplification orderings · term algebra · **KBO** · **demodulation** |
| **L6** §6.1–§6.12 | substitutions · Herbrand · **lifting** · unifiers · **the unification algorithm** |
| **L7** §7.1–§7.14 | non-ground KBO · **non-ground superposition** · subsumption · demodulation · general redundancy · **redundancy-checking workflow** |
| **Part E** | worked solutions to every published exercise, E.2.1 – E.7.3 |
| **App. A** | errata, per lecture, plus cross-lecture duplication and self-corrections |
| **App. B** | every rule on one page, plus the search framework and KBO in three lines |

---

## 1. Conventions fixed once and for all

The lectures switch notation between pages; the following is used consistently here.

**Clauses.** A clause is a disjunction of literals $L_1 \lor \dots \lor L_n$ with $n \ge 0$; the empty clause ($n=0$) is $\square$. Clauses with variables are implicitly universally quantified. A clause is **ground** if it contains no variables.

Two readings of a clause are in play, and the lectures never say which is in force where:

- **as a bag (finite multiset) of literals** — this is what L4 fixes "from now on", and it is what makes the clause ordering $\succ^{\text{bag}}$ work at all;
- **as a set of literals** — this is what the `⊆` in the subsumption definition of L7 literally means, and it is how derived clauses are normally stored (duplicates removed).

> **▸ Note (the choice matters twice).** Exercise 2.4 has the answer it does only under the **bag** reading; Exercise 7.2(a) has the answer the site gives only under the **bag** reading, while the definition printed two paragraphs earlier in the same lecture is the **set** reading. Both are flagged where they arise (§E.2.4, §7.10, §E.7.2). Throughout these notes: **bag for ordering, set for subsumption**, and duplicate literals in derived clauses are collapsed by factoring, which is noted explicitly wherever a derivation depends on it.

**Orderings.** $\succ$ is a strict (irreflexive, transitive) ordering. It is *well-founded* if there is no infinite descending chain $x_0 \succ x_1 \succ \dots$; *total* if any two distinct elements are comparable. $\succeq$ means "$\succ$ or $=$", and $s \not\succeq t$ means it is **not** the case that $s \succeq t$ — which, for a partial ordering, is weaker than $t \succ s$.

**Symbols.**

| Symbol | Meaning |
|---|---|
| $\succ$ | ordering on terms, atoms, literals, clauses (context disambiguates) |
| $\succ^{\text{bag}}$ | multiset extension of $\succ$ (usually written just $\succ$) |
| $\gg$ | **precedence**: a total ordering on the signature $\Sigma$ |
| $w$ | weight function $\Sigma \to \mathbb{N}$ (extended to variables in the non-ground case) |
| $\sigma$ | selection function (also used for substitutions in L6/L7 — see below) |
| $\theta, \tau$ | substitutions |
| $\mathbb{I}$ | a generic inference system |
| $\mathbb{BR}$ | binary resolution |
| $\mathbb{BR}\sigma$ | binary resolution with selection function $\sigma$ |
| $\mathbb{S}\mathrm{up}_{\succ,\sigma}$ | superposition with ordering $\succ$ and selection $\sigma$ |

> **▸ Fixed (naming clash).** The original uses $\sigma$ for *selection functions* in L2/L3/L4/L5 and for *substitutions* in L6/L7, and uses $\succ$ for both the precedence on symbols and the ordering on terms in L5's "Simplification Ordering" section. Here the precedence is always $\gg$, and where both a selection function and a substitution appear in the same rule the substitution is $\theta$.

**Literal ordering.** Given a well-founded ordering $\succ$ on atoms, L2 extends it to literals by two clauses:

- if $p \succ q$ then $p \succ \neg q$ and $\neg p \succ q$;
- $\neg p \succ p$.

Equivalently: compare **atoms first, polarity second**, with negative above positive.

$$L_1 \succ_{\text{lit}} L_2 \quad\text{iff}\quad \mathrm{atom}(L_1) \succ \mathrm{atom}(L_2), \ \text{ or } \ \mathrm{atom}(L_1) = \mathrm{atom}(L_2) \text{ and } L_1 = \neg A,\ L_2 = A.$$

So $\neg p_6 \succ p_6 \succ \neg p_5 \succ p_5 \succ \dots$ — in particular a *positive* literal on a big atom beats a *negative* literal on a small atom. This convention is what justifies the comparison $p_6 \succ \neg p_2$ used in the L4 clause-ordering example and in Exercise 3.4, and it is used without comment throughout L4–L7.

---

# Lecture 2 — Inference Systems and Selection Functions

## 2.1 Inference systems

- An **inference** has the form $\dfrac{F_1 \ \ \dots \ \ F_n}{G}$ with $n \ge 0$, where $F_1,\dots,F_n$ and $G$ are formulas.
- $G$ is the **conclusion**; $F_1,\dots,F_n$ are the **premises**.
- An **inference rule** $R$ is a *set* of inferences; each $I \in R$ is an **instance** of $R$.
- An **inference system** $\mathbb{I}$ is a set of inference rules.
- An **axiom** is an inference rule with no premises ($n = 0$).

Reading rules as sets of inferences is what lets a schematic rule such as $\frac{x+y=z}{|x+y=|z}$ stand for infinitely many concrete inferences. It is the same move that lifting (§6.6) will later perform for clauses.

## 2.2 A toy inference system

Represent the natural number $n$ by the string $\underbrace{|\dots|}_{n\ \text{times}}\varepsilon$. Six rules derive equalities between expressions built from these numerals, $+$, and $\cdot$:

$$\frac{}{\varepsilon = \varepsilon}\,(\varepsilon) \qquad \frac{x = y}{|x = |y}\,(|) \qquad \frac{}{\varepsilon + x = x}\,(+_1)$$

$$\frac{x + y = z}{|x + y = |z}\,(+_2) \qquad \frac{}{\varepsilon \cdot x = \varepsilon}\,(\cdot_1) \qquad \frac{x \cdot y = u \quad y + u = z}{|x \cdot y = z}\,(\cdot_2)$$

For example $\dfrac{||\varepsilon + |\varepsilon = |||\varepsilon}{|||\varepsilon + |\varepsilon = ||||\varepsilon}$ is an instance of $(+_2)$, and $\dfrac{}{\varepsilon + |||\varepsilon = |||\varepsilon}$ is an instance of the axiom $(+_1)$.

## 2.3 Derivation, proof

- A **derivation** in $\mathbb{I}$ is a tree built from inferences of $\mathbb{I}$. If its root is $E$, it is a derivation *of* $E$.
- A **proof** of $E$ is a *finite* derivation of $E$ whose leaves are all axioms.
- A **derivation of $E$ from $E_1,\dots,E_m$** is a finite derivation of $E$ each of whose leaves is either an axiom or one of $E_1,\dots,E_m$.

## 2.4 Clauses

- A **literal** is an atom $A$ or its negation $\neg A$.
- A **clause** is a disjunction $L_1 \lor \dots \lor L_n$, $n \ge 0$; the **empty clause** $\square$ has $n = 0$.
- A formula in **CNF** is a conjunction of clauses.
- A clause with variables is read as universally quantified: $p(x) \lor q(x)$ means $\forall x\,(p(x) \lor q(x))$.

## 2.5 Binary resolution $\mathbb{BR}$

$\mathbb{BR}$ is an inference system on propositional (equivalently, ground) clauses with two rules:

$$\frac{p \lor C_1 \qquad \neg p \lor C_2}{C_1 \lor C_2}\,(BR) \qquad\qquad \frac{L \lor L \lor C}{L \lor C}\,(Fact)$$

> **▸ Note (which factoring belongs to which system — the pages disagree).** Plain $\mathbb{BR}$ here factors an *arbitrary* literal $L$. The system $\mathbb{BR}\sigma$ of §2.8, and its restatement in L4, allow **positive factoring only** ($p \lor p \lor C \vdash p \lor C$). L7's non-ground system lists **both** positive and negative factoring. The three pages are not consistent about which factoring rules belong to which system; the summary in Appendix B records what each page actually prints rather than silently harmonising them.

## 2.6 Soundness

- An inference is **sound** if its conclusion is a logical consequence of its premises.
- An inference system is sound if every rule in it is sound.
- $\mathbb{BR}$ is sound.
- **Consequence.** If $\square$ is derivable from a clause set $S$ in $\mathbb{BR}$, then $S$ is unsatisfiable.

### Example

$$S = \{\ \neg p \lor \neg q,\quad \neg p \lor q,\quad p \lor \neg q,\quad p \lor q\ \}$$

is unsatisfiable: it forbids all four truth assignments to $p, q$. A $\mathbb{BR}$ refutation is given in §E.2.1, together with the reason there are infinitely many of them.

## 2.7 Selection functions

A **literal selection function** selects literals in a clause, subject to one requirement:

> if $C$ is non-empty, then at least one literal is selected in $C$.

Selected literals are underlined: $\underline{p} \lor \neg q$. Note that a "selection function" need not be a function of the clause at all — it can be any oracle that picks literals, and may depend on how the clause was derived.

## 2.8 Binary resolution with selection, $\mathbb{BR}\sigma$

A family of inference systems parameterised by a selection function $\sigma$. Inferences may only be applied to **selected** literals:

$$\frac{\underline{p} \lor C_1 \qquad \underline{\neg p} \lor C_2}{C_1 \lor C_2}\,(BR) \qquad\qquad \frac{\underline{p} \lor \underline{p} \lor C}{p \lor C}\,(Fact)$$

The point of selection is to cut the number of applicable inferences: instead of resolving on every complementary pair, a prover resolves only on the pairs the oracle nominates.

## 2.9 Selection alone destroys completeness

Restricting to selected literals is not free. **Binary resolution with an arbitrary selection function may be incomplete, even if factoring is unrestricted.** The lecture's counterexample:

$$\begin{array}{ll}
(1) & \neg q \lor \underline{r}\\
(2) & \neg p \lor \underline{q}\\
(3) & \neg r \lor \underline{\neg q}\\
(4) & \neg q \lor \underline{\neg p}\\
(5) & \neg p \lor \underline{\neg r}\\
(6) & \neg r \lor \underline{p}\\
(7) & r \lor q \lor \underline{p}
\end{array}$$

This set **is** unsatisfiable — here is a refutation ignoring selection:

$$\begin{array}{lll}
(8) & q \lor p & (6,7)\\
(9) & q & (2,8)\\
(10) & r & (1,9)\\
(11) & \neg q & (3,10)\\
(12) & \square & (9,11)
\end{array}$$

(Note the **linear** presentation of derivations — one numbered clause per line, with parent clauses cited. This is what Vampire and most provers print, and it is used for every derivation in these notes.)

But *with* the selection shown, every applicable inference produces a clause already in the set, or a clause containing one — so the process stalls and $\square$ is never derived.

## 2.10 Well-behaved selection functions

The cure is to constrain selection using an ordering. Fix an ordering $\succ$ on literals (§1).

> **Definition.** A literal selection function is **well-behaved** if, in every clause $C$, either
>
> - a **negative** literal is selected, **or**
> - **all** literals maximal in $C$ w.r.t. $\succ$ are selected.

Two consequences worth internalising, because every later worked example relies on them:

- A clause containing any negative literal can always be handled by selecting one negative literal, whatever the ordering. That is why in §E.5.4 selecting $f(b) \neq f(b)$ in clause (3) is immediately legitimate.
- In a **positive** clause there is no negative literal to fall back on, so all maximal literals must be selected. If the maximal literal is strictly maximal there is exactly one; otherwise **more than one literal must be selected** — e.g. in $p \lor p$ or $p(x) \lor p(y)$.

Why the counterexample of §2.9 is excluded: a well-behaved $\sigma$ selecting exactly those literals would force $r \succ q$ (from (1)), $q \succ p$ (from (2)) and $p \succ r$ (from (6)) — a cycle, so no ordering can support it.

## 2.11 Completeness of $\mathbb{BR}\sigma$

> **Theorem.** Binary resolution with selection is complete for **every** well-behaved selection function.

That is: if $S$ is unsatisfiable then $\square$ is derivable from $S$ in $\mathbb{BR}\sigma$. The freedom to pick any well-behaved $\sigma$ is what makes selection a practical heuristic knob rather than a fixed strategy — and §4.9 upgrades this theorem to the version a prover actually needs, one phrased in terms of a fair inference process rather than mere derivability.
---

# Lecture 3 — Saturation and Redundancy Elimination

*(L3 opens by repeating the "Soundness" and "Can this be used for checking (un)satisfiability?" sections of L2 verbatim, and closes by printing the two sections that L4 then opens with. Both duplications are dropped here; the L4 material appears in §4.1–§4.2.)*

## 3.1 The gap between completeness and search

Completeness says: if $S_0$ is unsatisfiable, **there exists** a derivation of $\square$ from $S_0$ in $\mathbb{I}$. That is an existence statement. It gives no hint how to *find* such a derivation, and the Ex-L2 exercise shows the search space is genuinely infinite even for a four-clause propositional problem (§E.2.1). So the search itself has to be formalised.

## 3.2 How to establish unsatisfiability

The idea:

- Keep a set of clauses $S$ — the **search space** — initially $S = S_0$.
- Repeatedly apply inferences of $\mathbb{I}$ to clauses in $S$ and add their conclusions to $S$, unless the conclusion is already there.
- If $\square$ ever appears, stop and report **unsatisfiable**.

## 3.3 How to establish satisfiability: saturated sets

When may we report *satisfiable*? When we have built a set closed under the calculus.

> **Definition.** $S$ is **saturated with respect to $\mathbb{I}$** ($\mathbb{I}$-saturated) if for every $\mathbb{I}$-inference with premises in $S$, the conclusion also belongs to $S$.
>
> The **$\mathbb{I}$-closure** of $S$ is the smallest set $S'$ containing $S$ and saturated with respect to $\mathbb{I}$.

In first-order logic saturated sets are usually infinite — this is forced by undecidability — so in practice one can never finish building one. The process of *trying* is what is called **saturation**, and it is the organising idea of the rest of the course.

## 3.4 Inference process

An **inference process** is a sequence of sets of formulas

$$S_0 \Rightarrow S_1 \Rightarrow S_2 \Rightarrow \dots$$

Each $(S_i \Rightarrow S_{i+1})$ is a **step**. The step is an $\mathbb{I}$-step if

1. there is an inference $\dfrac{F_1 \ \ \dots \ \ F_n}{F}$ in $\mathbb{I}$ with $\{F_1,\dots,F_n\} \subseteq S_i$, and
2. $S_{i+1} = S_i \cup \{F\}$.

An **$\mathbb{I}$-inference process** is one all of whose steps are $\mathbb{I}$-steps. Note that at this stage the process is purely **monotone**: clauses are only ever added. Deletion arrives in L4 (§4.7), and it changes the definition of the limit — see the warning in §3.6.

## 3.5 Property

> If $S_0 \Rightarrow S_1 \Rightarrow \dots$ is an $\mathbb{I}$-inference process and $F \in S_i$ for some $i$, then $F$ is derivable in $\mathbb{I}$ from $S_0$. In particular every $S_i$ is a subset of the $\mathbb{I}$-closure of $S_0$.

Nothing appears in the search space that was not already entailed by the input — the sanity condition that makes the whole scheme sound.

## 3.6 Limit of a process

$$S_\infty \;=\; \bigcup_i S_i$$

— the set of all derived formulas.

> **⚠ Two different definitions of $S_\infty$ are in circulation.** L3 defines the limit as the plain union $\bigcup_i S_i$, which is correct here because no step ever deletes. L4 (§4.8), where deletion is allowed, defines it instead as the set of **persistent** clauses $\bigcup_i \bigcap_{j \ge i} S_j$. The two agree exactly when nothing is deleted. Read "$S_\infty$" as the persistent-clause version from L4 onwards.

**Question posed by the lecture.** Suppose $S_0$ is unsatisfiable and we run an infinite $\mathbb{BR}$-inference process. Does completeness imply $\square \in S_\infty$?

**Answer: no** — not without a further condition. Completeness guarantees that *some* derivation of $\square$ exists, but an inference process is free to spend eternity on other inferences and never perform the ones that derivation needs. That further condition is fairness.

## 3.7 Fairness

> **Definition.** An inference process with limit $S_\infty$ is **fair** if for every $\mathbb{I}$-inference
> $$\frac{F_1 \ \ \dots \ \ F_n}{F},$$
> whenever $\{F_1,\dots,F_n\} \subseteq S_\infty$, there exists $i$ with $F \in S_i$.

In words: **no inference between formulas that survive is postponed forever.** Note the conclusion is required to appear in *some* $S_i$, not in $S_\infty$ — a distinction that is vacuous here but becomes essential in L4, where a conclusion may be generated and then deleted again as redundant.

## 3.8 Limit of a fair inference process

> **Exercise (published as Ex 3.1).** Let $S_0 \Rightarrow S_1 \Rightarrow \dots$ be a fair $\mathbb{I}$-inference process. Show that its limit $S_\infty$ is the $\mathbb{I}$-closure of $S_0$.

Solved in §E.3.1. The moral: *fairness is exactly the condition that turns "run inferences forever" into "compute the closure."* Everything a saturation prover does is an approximation of this.

## 3.9 Completeness, reformulated

> **Theorem.** For an inference system $\mathbb{I}$, the following are equivalent.
>
> 1. $\mathbb{I}$ is complete.
> 2. For every unsatisfiable $S_0$ and every fair $\mathbb{I}$-inference process starting from $S_0$, the limit $S_\infty$ contains $\square$.

This is the form of completeness a theorem prover can act on: it no longer says "a proof exists somewhere", it says "**this** procedure will find one, provided it is fair." Compare §4.9, which restates it once more for processes that also delete.

## 3.10 Fair saturation algorithms: inference selection by clause selection

Fairness is a property of an infinite process; an implementation needs a scheduling rule that guarantees it. The standard one is the **given-clause algorithm**: repeatedly pick a **given clause** from the candidate clauses, perform all inferences between it and previously selected clauses, and add the resulting **children** back to the search space. Fairness is then secured by choosing given clauses so that every clause is eventually selected (e.g. alternating between "lightest first" and "oldest first").

Since inferences are only ever applied to the given clause and to clauses already selected, the search space splits in two:

- **active** clauses — already selected; they participate in inferences;
- **passive** clauses — waiting; they do not.

> **Observation.** The passive set is normally far larger than the active set — often by **2–4 orders of magnitude**, depending on the algorithm and the problem. This asymmetry is why the passive set is the data structure that gets optimised, and why cheap retention tests that discard passive clauses early (§7.14) pay off so much.

## 3.11 Saturation algorithm

> A **saturation algorithm** is an algorithm that tries to saturate a set of clauses with respect to a given inference system.

**In theory** there are three scenarios:

1. $\square$ is generated ⇒ the input set is **unsatisfiable**.
2. Saturation terminates without generating $\square$ ⇒ the input set is **satisfiable**.
3. Saturation runs forever without generating $\square$ ⇒ the input set is **satisfiable**.

**In practice** the third scenario is different:

1. $\square$ is generated ⇒ **unsatisfiable**.
2. Saturation terminates without generating $\square$ ⇒ **satisfiable**.
3. Saturation runs until resources are exhausted, without generating $\square$ ⇒ **unknown**.

Cases 1 and 2 are the same in both lists; the whole difference between the theory and the practice of first-order theorem proving lives in case 3. Case 2 is also why saturation is worth doing at all on satisfiable input: a terminating saturation is a *proof of satisfiability*, and §4.10 notes it can even certify formulas whose only models are infinite.

## 3.12 Where redundancy comes in

Two deletion rules have been known to be sound since 1965:

- a **propositional tautology** — a clause of the form $p \lor \neg p \lor C$, containing a complementary pair — may be deleted;
- a **subsumed** clause may be deleted: $C$ subsumes $C \lor D$ for non-empty $D$.

There are also **equational tautologies**, e.g. $a \neq b \lor b \neq c \lor f(c,c) = f(a,a)$.

Deleting clauses breaks the monotone picture of §3.4: a clause can now leave the search space, so "the limit" has to be redefined (§3.6, §4.8) and fairness has to be re-checked. Rather than argue case by case that each deletion rule preserves completeness, L4 builds a general **theory of redundancy** that covers all of them at once. That is the subject of the next lecture.
---

# Lecture 4 — Redundancy Elimination and Equality

*(L4 opens by repeating the last two sections of L3 — "Subsumption and Tautology Deletion" and "Problem" — verbatim. They are given once, here.)*

## 4.1 Subsumption and tautology deletion

A clause is a **propositional tautology** if it has the form $p \lor \neg p \lor C$, i.e. it contains a complementary pair of literals.

There are also **equational tautologies**, e.g.

$$a \neq b \ \lor\ b \neq c \ \lor\ f(c,c) = f(a,a)$$

(if $a = b$ and $b = c$ then $a = c$, hence $f(c,c) = f(a,a)$ by congruence — so no interpretation falsifies the clause).

A clause $C$ **subsumes** any clause $C \lor D$ where $D$ is non-empty. (This is the ground/propositional special case; the general definition with a substitution is in §7.10.)

Since 1965 it has been known that subsumed clauses and propositional tautologies can be removed from the search space without losing completeness.

## 4.2 The problem

- How do we *prove* that completeness is preserved when we remove subsumed clauses and tautologies?
- Answer: don't argue case by case — build a general **theory of redundancy**.

## 4.3 Multiset (bag) extension of an ordering

A **bag** is a finite multiset. Let $\succ$ be a strict ordering on a set $X$. Its **bag extension** $\succ^{\text{bag}}$ is the smallest transitive relation on bags over $X$ such that

$$\{x, y_1,\dots,y_n\} \ \succ^{\text{bag}}\ \{x_1,\dots,x_m,y_1,\dots,y_n\} \qquad \text{if } x \succ x_i \text{ for all } i \in \{1,\dots,m\},$$

where $m \ge 0$.

**Idea:** a bag gets smaller when you replace one element by *any finite number* (possibly zero) of strictly smaller elements.

Two consequences worth remembering, both used constantly later:

- taking $m = 0$: **removing** an element makes a bag smaller, so a proper superset is always greater than its subset;
- known results: (1) $\succ^{\text{bag}}$ is an ordering; (2) if $\succ$ is total so is $\succ^{\text{bag}}$; (3) if $\succ$ is well-founded so is $\succ^{\text{bag}}$.

An equivalent and often handier characterisation: $M \succ^{\text{bag}} N$ iff $M \neq N$ and for every $y \in N \setminus M$ there is some $x \in M \setminus N$ with $x \succ y$ (differences taken as multisets).

## 4.4 Clause orderings

From now on a clause *is* a bag of literals. We have an ordering $\succ$ on literals (§1), so we can compare clauses by $\succ^{\text{bag}}$. For simplicity the multiset ordering is also written $\succ$.

### Worked example

Let $\succ$ be total and well-founded on the ground atoms $p_1,\dots,p_6$ with $p_6 \succ p_5 \succ p_4 \succ p_3 \succ p_2 \succ p_1$, and use the literal ordering of §1. Order

$$p_6 \lor \neg p_6, \qquad \neg p_2 \lor p_4 \lor p_5, \qquad p_2 \lor p_3 .$$

**▸ Completed (L4 poses this and stops; the answer is on the Ex-L3 page as Problem 3.4, and is reproduced with its own justification in §E.3.4).**

As multisets: $A = \{p_6, \neg p_6\}$, $B = \{\neg p_2, p_4, p_5\}$, $C = \{p_2, p_3\}$.

- $A \succ B$: $A \setminus B = \{p_6, \neg p_6\}$ and $B \setminus A = \{\neg p_2, p_4, p_5\}$; the element $\neg p_6 \in A$ dominates all three (atom $p_6$ is the largest atom), so $A \succ B$.
- $B \succ C$: $B\setminus C = \{\neg p_2, p_4, p_5\}$, $C \setminus B = \{p_2, p_3\}$; $p_4 \succ p_3$ and $p_4 \succ p_2$, so $B \succ C$.

$$\boxed{\;p_6 \lor \neg p_6 \ \succ\ \neg p_2 \lor p_4 \lor p_5 \ \succ\ p_2 \lor p_3\;}$$

Note the tautology is the *largest* clause — which is exactly why tautologies are cheap to delete.

## 4.5 Redundancy

> **Definition.** A clause $C \in S$ is **redundant** in $S$ if it is a logical consequence of clauses in $S$ that are **strictly smaller than $C$**. Writing $S_{\prec C}$ for $\{D \in S : C \succ D\}$, this is $S_{\prec C} \models C$.

### Examples

**Tautologies.** $\models p \lor \neg p \lor C$, so a tautology follows from the *empty* set of premises — vacuously a set of smaller clauses. Redundant.

**Subsumed clauses.** $C$ subsumes $C \lor D$ with $D$ non-empty. Then

$$C \lor D \succ C \qquad\text{and}\qquad C \models C \lor D,$$

so $C \lor D$ is redundant. (The first line is the "superset is bigger" property of §4.3.)

**Everything, once you have $\square$.** If $\square \in S$ then every other clause of $S$ is redundant: $\square$ is smaller than every non-empty clause and $\square \models C$ for every $C$. This is why a prover stops the moment it derives $\square$.

## 4.6 Redundant clauses can be removed

In $\mathbb{BR}\sigma$ — and in every calculus considered later — redundant clauses can be deleted from the search space without losing completeness.

## 4.7 Inference process with redundancy

Let $\mathbb{I}$ be an inference system. Extending §3.4, an inference process now has steps $S_i \Rightarrow S_{i+1}$ of **two** kinds:

1. **Add** the conclusion of an $\mathbb{I}$-inference whose premises are in $S_i$.
2. **Delete** a clause redundant in $S_i$: $S_{i+1} = S_i - \{C\}$ where $C$ is redundant in $S_i$.

Step 2 is the new one, and it is what forces the redefinitions that follow.

## 4.8 Fairness: persistent clauses and the limit

For a process $S_0 \Rightarrow S_1 \Rightarrow S_2 \Rightarrow \dots$, a clause $C$ is **persistent** if

$$\exists i\, \forall j \ge i\ (C \in S_j).$$

The **limit** is the set of persistent clauses:

$$S_\infty \;=\; \bigcup_{i = 0,1,\dots}\ \ \bigcap_{j \ge i} S_j .$$

The process is **$\mathbb{I}$-fair** if every inference whose premises are all persistent has been performed: if

$$\frac{C_1 \quad \dots \quad C_n}{C}$$

is an $\mathbb{I}$-inference with $\{C_1,\dots,C_n\} \subseteq S_\infty$, then $C \in S_i$ for some $i$.

Two things changed relative to §3.6–§3.7, and both are consequences of allowing deletion:

- The limit is no longer $\bigcup_i S_i$ but the **persistent** clauses. A clause that is added and later deleted is not in the limit.
- "$C \in S_i$ for *some* $i$" now does real work: the conclusion is allowed to be generated and then deleted again as redundant, which is exactly what a simplifying inference does.

## 4.9 Completeness of $\mathbb{BR}\sigma$

> **Completeness Theorem.** Let $\succ$ be a well-founded ordering and $\sigma$ a well-behaved selection function (§2.10). Let $S_0$ be a set of clauses and let $S_0 \Rightarrow S_1 \Rightarrow S_2 \Rightarrow \dots$ be a fair $\mathbb{BR}\sigma$-inference process. Then $S_0$ is unsatisfiable **iff** $\square \in S_i$ for some $i$.

This is §2.11 and §3.9 combined and upgraded: completeness now survives deletion of redundant clauses.

## 4.10 Saturation up to redundancy

> **Definition.** $S$ is **saturated up to redundancy** if for every $\mathbb{I}$-inference
> $$\frac{C_1 \quad \dots \quad C_n}{C}$$
> with premises in $S$, either $C \in S$, or $C$ is redundant w.r.t. $S$ (i.e. $S_{\prec C} \models C$).

Compare §3.3: plain saturation demanded $C \in S$ outright. Saturation up to redundancy is the weaker, achievable version.

> **Lemma.** A set $S$ saturated up to redundancy is unsatisfiable iff $\square \in S$.

**▸ Fixed.** The lecture then concludes: *"Therefore, if we built a set saturated up to redundancy, then the initial set $S_0$ is satisfiable. This is a powerful way of checking redundancy."* Both halves are wrong as written. The correct statement:

> Therefore, if we build a set saturated up to redundancy **that does not contain $\square$**, then the initial set $S_0$ is **satisfiable**. This is a powerful way of checking **satisfiability** — one can even establish satisfiability of formulas that have only infinite models.

Without the side condition the claim is absurd (a saturated set containing $\square$ would prove everything satisfiable); and "checking redundancy" is a slip for "checking satisfiability". This is scenario 2 of §3.11.

**▸ Clarification.** The lecture adds: *"the only problem is that there is no obvious way to build a model of $S_0$ out of a saturated set."* This needs qualifying. The standard completeness proof (Bachmair–Ganzinger) *does* construct a model — the candidate/Herbrand model built by induction over the clause ordering. What is true is that the model so obtained can be infinite and is not returned as a finite, directly inspectable object, which is why saturation-based satisfiability answers are less useful in practice than finite-model finding.

## 4.11 Why the ordering conditions are there

One key property makes the redundancy lemma work:

> **the conclusion of every rule is strictly smaller than the rightmost premise.**

(*The published text says "smaller **that** the rightmost premise".*) For binary resolution with selection:

$$\frac{\underline{p} \lor C_1 \qquad \underline{\neg p} \lor C_2}{C_1 \lor C_2}\ (BR) \qquad\qquad \frac{\underline{p} \lor \underline{p} \lor C}{p \lor C}\ (Fact)$$

For $(BR)$ the rightmost premise is $\neg p \lor C_2$; the conclusion drops $\neg p$ and adds the literals of $C_1$, all of which are $\prec \neg p$ because $\neg p$ is selected and $\sigma$ is well-behaved. This is exactly the bag-extension step of §4.3, and it is the abstract content of Exercise 3.2 (§E.3.2).

## 4.12 First-order logic with equality

Equality is a distinguished predicate $=$; an equality is $l = r$.

**▸ Fixed.** The lecture says *"The order of literals in equalities does not matter"*. It should say **the order of the two sides (terms) of an equality does not matter**: an equality $l = r$ is treated as the *multiset of its two terms* $\{l, r\}$, so $l = r$ and $r = l$ are the same literal. (Nothing here is being said about the order of literals in a clause.) The lecture's own next clause gets this right — "we consider an equality $l = r$ as a multiset consisting of two terms $l, r$" — so only the lead-in sentence is at fault. The convention is used constantly: e.g. in Exercise 7.3, where the axiom $x = f(c)$ is silently rewritten as $f(c) = x$.

## 4.13 Equality: an axiomatisation (recap)

- **reflexivity**: $x = x$
- **symmetry**: $x = y \rightarrow y = x$
- **transitivity**: $x = y \land y = z \rightarrow x = z$
- **function congruence**, for every function symbol $f$:
  $$x_1 = y_1 \land \dots \land x_n = y_n \ \rightarrow\ f(x_1,\dots,x_n) = f(y_1,\dots,y_n)$$
- **predicate congruence**, for every predicate symbol $P$:
  $$x_1 = y_1 \land \dots \land x_n = y_n \land P(x_1,\dots,x_n) \ \rightarrow\ P(y_1,\dots,y_n)$$

Adding these axioms is *complete* but hopeless in practice — they generate enormous numbers of useless inferences. Hence a dedicated calculus.

## 4.14 Inference systems for logic with equality — the plan

We define a resolution + superposition system. It is complete and admits redundancy elimination. We build it in two stages:

1. Prove completeness for **ground** clauses only.
2. **Lift** it to arbitrary first-order clauses (Lecture 6).

The same staging applies to the ingredients: the ordering and the selection function are first defined on ground clauses, then generalised.

## 4.15 Simple ground superposition (no ordering conditions yet)

**Superposition (right and left):**

$$\frac{\ l = r\ \lor C \qquad\ s[l] = t\ \lor D}{s[r] = t \lor C \lor D}\,(Sup) \qquad\qquad \frac{\ l = r\ \lor C \qquad\ s[l] \neq t\ \lor D}{s[r] \neq t \lor C \lor D}\,(Sup)$$

**Equality resolution:**

$$\frac{\ s \neq s\ \lor C}{C}\,(ER)$$

**Equality factoring:**

$$\frac{\ s = t\ \lor\ s = t'\ \lor C}{s = t \lor t \neq t' \lor C}\,(EF)$$

## 4.16 Worked example

**▸ Completed.** The lecture displays this clause set with no instructions and no solution:

$$\begin{array}{ll}
(1) & f(a) = a \lor g(a) = a\\
(2) & f(f(a)) = a \lor g(g(a)) \neq a\\
(3) & f(f(a)) \neq a
\end{array}$$

**Task (reconstructed):** show that $S = \{(1),(2),(3)\}$ is unsatisfiable using the simple ground superposition system above.

*First, a semantic sanity check.* By (3), $f(f(a)) \neq a$. If $f(a) = a$ then $f(f(a)) = f(a) = a$, contradicting (3); so by (1) we need $g(a) = a$. But then $g(g(a)) = g(a) = a$, so by (2) we need $f(f(a)) = a$ — contradicting (3) again. So $S$ is indeed unsatisfiable.

*Refutation.*

| # | Clause | From |
|---|---|---|
| (4) | $f(a) \neq a \lor g(a) = a$ | $Sup$ of (1) into (3): rewrite the inner $f(a) \to a$ inside $f(f(a))$ |
| (5) | $a \neq a \lor g(a) = a$ | $Sup$ of (1) into (4): rewrite $f(a) \to a$; **duplicate collapsed**, see below |
| (6) | $g(a) = a$ | $ER$ on (5) |
| (7) | $f(f(a)) = a \lor g(a) \neq a$ | $Sup$ of (6) into (2): rewrite the inner $g(a) \to a$ inside $g(g(a))$ |
| (8) | $f(f(a)) = a \lor a \neq a$ | $Sup$ of (6) into (7) |
| (9) | $f(f(a)) = a$ | $ER$ on (8) |
| (10) | $a \neq a$ | $Sup$ of (9) into (3) |
| (11) | $\square$ | $ER$ on (10) |

**▸ Note (where the two clause readings collide).** Step (5) superposes (1) into (4). The left premise contributes $C = (g(a)=a)$ and the right premise contributes $D = (g(a)=a)$, so as a **bag** the conclusion is

$$a \neq a \ \lor\ g(a) = a \ \lor\ g(a) = a,$$

three literals. Writing it as two literals, as above, silently collapses the duplicate. Under the bag convention of §4.4 this needs one extra step — positive factoring on the two copies of $g(a) = a$ — before (5) is written as shown. Implementations keep clauses duplicate-free and so perform the collapse automatically; the lecture never says which convention is in force. Step (8) is unaffected, since there $D$ is empty.

## 4.17 Can this system be used for efficient theorem proving?

Not really — far too many inferences. From the single clause $f(a) = a$ one can derive **every** clause of the form

$$f^m(a) = f^n(a), \qquad m,n \ge 0,$$

and, worst of all, the derived clauses can be arbitrarily *larger* than the premise. The cure is the three ingredients already introduced:

1. an ordering,
2. literal selection,
3. redundancy elimination.
---

# Lecture 5 — Term Orderings

*(L5 opens by repeating §4.15–§4.17 verbatim; that repetition is dropped here.)*

## 5.1 Ordering equality atoms and literals

An equality atom $s = t$ is compared as the multiset $\{s,t\}$, so for two equalities of the same polarity:

$$(s' = t') \succ_{\text{lit}} (s = t) \quad\text{iff}\quad \{s',t'\} \succ^{\text{bag}} \{s,t\}$$
$$(s' \neq t') \succ_{\text{lit}} (s \neq t) \quad\text{iff}\quad \{s',t'\} \succ^{\text{bag}} \{s,t\}$$

**▸ Completed.** As published the definition covers only positive-vs-positive and negative-vs-negative — it never says how to compare $s = t$ with $s' \neq t'$, so it does not define a total ordering on literals at all, even though totality is required by the completeness proof and is used in every worked example. (Contrast §1: for *non-equality* literals L2 does define the mixed case.) The standard completion encodes polarity into the multiset:

$$s = t \ \mapsto\ \{\{s\},\{t\}\}, \qquad\qquad s \neq t \ \mapsto\ \{\{s,t\}\}$$

and compares these *multisets of multisets* by the twice-iterated bag extension. The effect worth memorising:

- **on the same atom, the negative literal is bigger:** $(s \neq t) \succ (s = t)$;
- otherwise the comparison is driven by the larger of the two sides.

This is the equality analogue of the "$\neg A \succ A$" clause of §1.

## 5.2 Ground superposition $\mathbb{S}\mathrm{up}_{\succ,\sigma}$

Let $\sigma$ be a well-behaved literal selection function (§2.10); selected literals are underlined.

**Superposition (right and left):**

$$\frac{\underline{l = r} \lor C \qquad \underline{s[l] = t} \lor D}{s[r] = t \lor C \lor D}\,(Sup) \qquad\qquad \frac{\underline{l = r} \lor C \qquad \underline{s[l] \neq t} \lor D}{s[r] \neq t \lor C \lor D}\,(Sup)$$

where

1. $l \succ r$;
2. $s[l] \succ t$;
3. $l = r$ is strictly greater than any literal in $C$;
4. *(superposition-right only)* $s[l] = t$ is greater than or equal to any literal in $D$.

**Equality resolution:**

$$\frac{\underline{s \neq s} \lor C}{C}\,(ER)$$

**Equality factoring:**

$$\frac{\underline{s = t} \lor s = t' \lor C}{s = t \lor t \neq t' \lor C}\,(EF)$$

where

1. $s \succ t \succeq t'$;
2. $s = t$ is strictly greater than any literal in $C$.

Read the conditions as: *only rewrite big things into small things, and only at the biggest literal of a clause.* That is what stops the $f^m(a) = f^n(a)$ explosion of §4.17.

## 5.3 Extension to arbitrary (non-equality) literals

A neat trick that lets one calculus handle everything:

- work in a two-sorted logic where **equality is the only predicate**;
- terms are of sort 1, non-equality atoms become terms of sort 2;
- add a constant $\top$ of sort 2;
- replace each atom $p(t_1,\dots,t_n)$ by the sort-2 equality $p(t_1,\dots,t_n) = \top$.

Example:

$$p(a,b) \lor \neg q(a) \lor a \neq b \qquad\rightsquigarrow\qquad p(a,b) = \top \ \lor\ q(a) \neq \top \ \lor\ a \neq b$$

## 5.4 Binary resolution as superposition

Ignoring selection functions, binary resolution

$$\frac{A \lor C_1 \qquad \neg A \lor C_2}{C_1 \lor C_2}\,(BR)$$

is simulated by one superposition step followed by one equality resolution:

$$\frac{A = \top \lor C_1 \qquad A \neq \top \lor C_2}{\dfrac{\top \neq \top \lor C_1 \lor C_2}{C_1 \lor C_2}\,(ER)}\,(Sup)$$

**Exercise 5.A.** *Show that* positive factoring can also be simulated in the superposition system. **▸ Fixed:** the lecture states this as a fact under the heading "Exercise"; it is meant as a task. Solution in §E.4.4 (it is also, verbatim, published Exercise 5.1).

## 5.5 Simplification orderings

When equality enters, we need orderings on **terms**. Fix a well-founded strict precedence $\gg$ on the signature. An ordering $\succ$ on terms is a **simplification ordering** if

1. $\succ$ is well-founded;
2. $\succ$ is **monotonic** (compatible with contexts): $l \succ r$ implies $s[l] \succ s[r]$;
3. $\succ$ is **stable under substitutions**: $l \succ r$ implies $l\theta \succ r\theta$.

Conditions 2 and 3 combine into

> **2a.** if $l \succ r$ then $s[l\theta] \succ s[r\theta]$.

**▸ Clarification.** Many textbooks add the **subterm property** ($t[s] \succ s$ for every proper subterm $s$) to this list. Here it is not assumed but derived in the weaker form of §5.6; KBO and LPO satisfy the full subterm property.

## 5.6 A general property of term orderings

> If $\succ$ is a simplification ordering, then for every term $t[s]$ and every proper subterm $s$ of it, $s \not\succ t[s]$.

**Why this matters — an example.** Consider

$$f(a) = a, \qquad f(f(a)) = a, \qquad f(f(f(a))) = a .$$

Relative to this set, $f(f(a)) = a$ and $f(f(f(a))) = a$ are both **redundant**: each follows from $f(a) = a$, and each is strictly greater than it (bigger terms). Meanwhile $f(a) = a$ *is* a logical consequence of $\{f(f(a)) = a,\ f(f(f(a))) = a\}$ — substitute the first into the second — but it is **not** redundant with respect to that set, because both premises are *larger* than it. Redundancy is not the same as entailment: the ordering does real work.

**▸ Fixed (missing "with respect to what").** The lecture says only "both … are redundant", without naming the set. Redundancy is always relative to a set of clauses; the intended reading is *redundant with respect to a set containing $f(a) = a$*.

**Exercise 5.B.** Show that $\{f(a) = a,\ f(f(f(a))) \neq a\}$ is unsatisfiable, using superposition with redundancy elimination.

**▸ Completed (no solution was published).** With any simplification ordering, $f(a) \succ a$, so the unit equality is oriented left-to-right and can be used as a **demodulator** (§5.10). Rewriting the second clause repeatedly:

$$f(f(f(a))) \neq a \ \xrightarrow{\ f(a) \to a\ } \ f(f(a)) \neq a \ \xrightarrow{\ f(a)\to a\ } \ f(a) \neq a \ \xrightarrow{\ f(a) \to a\ } \ a \neq a$$

Each step is a superposition whose right premise becomes redundant and is deleted (demodulation), so the search space never grows. Finally $ER$ on $a \neq a$ gives $\square$. Total: three simplifying steps and one $ER$ — no clause is ever larger than one already present.

## 5.7 Term algebra

The **term algebra** $\mathrm{TA}(\Sigma)$ of a signature $\Sigma$:

- **Domain**: the set of all ground terms over $\Sigma$;
- **Interpretation** of each function symbol $f$ and constant $c$:

$$f_{\mathrm{TA}(\Sigma)}(t_1,\dots,t_n) \ \stackrel{\text{def}}{=}\ f(t_1,\dots,t_n), \qquad\qquad c_{\mathrm{TA}(\Sigma)} \ \stackrel{\text{def}}{=}\ c .$$

**▸ Fixed.** The original writes these with $\stackrel{\text{def}}{\Leftrightarrow}$ (an *iff* connective, appropriate for formulas, not for terms), and switches from lowercase $c$ in the prose to uppercase $C$ in the display. Both corrected above.

Each ground term denotes *itself*: the term algebra is the free/Herbrand structure over $\Sigma$, which is why an ordering on ground terms is simultaneously an ordering on domain elements.

## 5.8 Knuth–Bendix Ordering (KBO), ground case

*(The lecture gives this section twice, under "Ground Case" and "Ground Case: Summary"; the only difference is that the second copy appends the admissibility note. Merged here.)*

Fix:

- a signature $\Sigma$ (inducing $\mathrm{TA}(\Sigma)$);
- a total precedence $\gg$ on $\Sigma$;
- a weight function $w : \Sigma \to \mathbb{N}$.

The **weight** of a ground term:

$$|g(t_1,\dots,t_n)| \;=\; w(g) + \sum_{i=1}^{n} |t_i| .$$

Then $g(t_1,\dots,t_n) \succ_{\text{KB}} h(s_1,\dots,s_m)$ iff

1. $|g(t_1,\dots,t_n)| > |h(s_1,\dots,s_m)|$ *(by weight)*; **or**
2. the weights are equal and either
   - **2.1** $g \gg h$ *(by precedence)*, or
   - **2.2** $g = h$ (so $n = m$) and for some $1 \le i \le n$: $t_1 = s_1, \dots, t_{i-1} = s_{i-1}$ and $t_i \succ_{\text{KB}} s_i$ *(lexicographic, left to right)*.

KBO is the main ordering used in Vampire and in essentially all resolution/superposition provers.

### Weight functions are not arbitrary — admissibility

$w : \Sigma \to \mathbb{N}$ must satisfy:

- $w(a) > 0$ for every constant $a \in \Sigma$;
- if $w(f) = 0$ for a **unary** $f \in \Sigma$, then $f \gg g$ for every $g \in \Sigma$ with $g \neq f$, i.e. $f$ is the **greatest** symbol in the precedence.

Consequently **at most one unary function may have weight 0**.

*Why?* Compare $a$ with $f(a)$ under an arbitrary $\gg$ and $w$: if $w(f) = 0$ the two have equal weight and only the precedence can break the tie; if $f$ were not maximal we would get $a \succ f(a)$, destroying the subterm property and with it well-foundedness of the ordering on the (infinite) term algebra.

### Example

$$w(a) = 1,\quad w(b) = 2,\quad w(f) = 3,\quad w(g) = 0$$

$$|f(g(a), f(a,b))| = |3(0(1),\,3(1,2))| = 3 + 0 + 1 + 3 + 1 + 2 = 10$$

**▸ Clarification.** Two things go unsaid here. (i) $f$ is used as a **binary** symbol in this example, whereas $f$ is unary elsewhere in the lecture — they are different symbols. (ii) $w(g) = 0$ with $g$ unary is only admissible if $g$ is the greatest symbol of $\Sigma$ w.r.t. $\gg$; the example never fixes a precedence, so implicitly $g \gg f \gg b \gg a$ (or any precedence with $g$ on top).

## 5.9 The conclusion is smaller than the rightmost premise

The property that made redundancy work for $\mathbb{BR}\sigma$ (§4.11) holds for superposition too:

$$\frac{\underline{l = r} \lor C \qquad \underline{s[l] = t} \lor D}{s[r] = t \lor C \lor D}\,(Sup) \qquad\qquad \frac{\underline{l = r} \lor C \qquad \underline{s[l] \neq t} \lor D}{s[r] \neq t \lor C \lor D}\,(Sup)$$

with (1) $l \succ r$; (2) $s[l] \succ t$; (3) $l = r$ strictly greater than any literal in $C$; (4) $s[l] = t$ greater than or equal to any literal in $D$.

Since $l \succ r$ and $\succ$ is monotonic, $s[l] \succ s[r]$, hence $s[l] = t \succ s[r] = t$: the rewritten literal shrinks, and conditions (3)–(4) ensure nothing else in the conclusion outweighs it.

## 5.10 New redundancy: demodulation

Take a superposition whose left premise is a **unit** equality:

$$\frac{\underline{l = r} \qquad \underline{s[l] = t} \lor D}{s[r] = t \lor D}\,(Sup)$$

Observe:

$$l = r,\quad s[r] = t \lor D \ \models\ s[l] = t \lor D \qquad\text{and}\qquad s[l] = t \lor D \ \succ\ s[r] = t \lor D .$$

So if additionally

$$s[l] = t \lor D \ \succ\ l = r,$$

the right premise is a consequence of *strictly smaller* clauses (the conclusion and the left premise) — it is redundant and may be **deleted**.

This rule — superposition **plus deletion of the premise** — is **demodulation** (rewriting by unit equalities). It is the single most valuable simplification rule in practice: it keeps the search space from growing.

**Exercise 5.C** (published as the last exercise of L5, and as Exercise 5.5): saturate $\{a = b \lor a = c,\ f(a) \neq f(b),\ b = c\}$ under KBO with $f \gg a \gg b \gg c$ and all weights 1; challenge: derive $\square$ generating only four new clauses. Solution in §E.5.5.

**▸ Fixed.** The exercise says "the set $S$ of ground **formulas**"; the objects listed are ground **clauses**, and the calculus applies to clauses.

---

# Lecture 6 — Unification and Lifting

## 6.1 Warm-up: which of these are true?

1. First-order logic is an extension of propositional logic.
2. First-order logic is NP-complete.
3. In first-order logic you can quantify over sets.
4. First-order logic is decidable.
5. One can axiomatise the naturals in first-order logic.
6. Having proofs is good.

**▸ Completed (no answers were published).**

| | Verdict | Why |
|---|---|---|
| 1 | **True** | Propositional logic is the fragment with only 0-ary predicates and no quantifiers. |
| 2 | **False** | Validity in FOL is undecidable, hence not in NP. It is *recursively enumerable* (semi-decidable) — that is the best one gets. NP-completeness is a property of e.g. propositional SAT. |
| 3 | **False** | Quantification over sets/predicates is second-order. FOL quantifies over individuals only. (One can *simulate* set talk with a membership predicate and axioms, but that is not the same thing.) |
| 4 | **False** | Church–Turing: validity is undecidable. Satisfiability of a FOL sentence is co-r.e. Decidable fragments exist (monadic, two-variable, Bernays–Schönfinkel…). |
| 5 | **True, with a caveat** | One can *write down* first-order axioms for arithmetic (Peano arithmetic, with an induction *schema* rather than a single second-order induction axiom). But no first-order theory pins the naturals down: by compactness/Löwenheim–Skolem, PA has non-standard models, and by Gödel true arithmetic is not recursively axiomatisable. So "axiomatise" yes, "characterise up to isomorphism" no. |
| 6 | **True** (the intended joke) | A proof is a certificate: it can be checked independently, minimised, and turned into an explanation. It is the reason saturation provers output derivations rather than just "unsat". |

## 6.2 Substitutions

A **substitution** $\theta$ maps variables to terms such that $\{x \mid \theta(x) \neq x\}$ is finite; that set is the **domain** of $\theta$. Notation $\{x_1 \mapsto t_1,\dots,x_n \mapsto t_n\}$ with the $x_i$ pairwise distinct:

$$\theta(x) = \begin{cases} t_i & \text{if } x = x_i\\ x & \text{if } x \notin \{x_1,\dots,x_n\}\end{cases}$$

Applying $\theta$ to an expression $E$ replaces each $x_i$ by $t_i$ **simultaneously**; the result is $E\theta$. Substitutions are functions, so they compose; we write $\theta_1\theta_2$ (rather than $\theta_2 \circ \theta_1$) and always have $E(\theta_1\theta_2) = (E\theta_1)\theta_2$.

**Example.** $E = p(x, y, f(a))$ and $\theta = \{x \mapsto b,\ y \mapsto x\}$. What is $E\theta$?

**▸ Completed:** $E\theta = p(b,\, x,\, f(a))$. The replacement is simultaneous: $y$ becomes $x$, and that new $x$ is **not** then replaced by $b$. (Sequential application would wrongly give $p(b,b,f(a))$.)

## 6.3 Substitution composition

Given

$$\theta_1 = \{x_1 \mapsto s_1,\dots,x_m \mapsto s_m\}, \qquad \theta_2 = \{y_1 \mapsto t_1,\dots,y_n \mapsto t_n\},$$

the composition $\theta_1\theta_2$ is obtained from

$$\{x_1 \mapsto s_1\theta_2,\ \dots,\ x_m \mapsto s_m\theta_2,\ y_1 \mapsto t_1,\ \dots,\ y_n \mapsto t_n\}$$

by deleting

1. every $y_i \mapsto t_i$ with $y_i \in \{x_1,\dots,x_m\}$ (the $\theta_1$ binding wins);
2. every $x_i \mapsto s_i\theta_2$ with $x_i = s_i\theta_2$ (identity bindings are dropped).

**Example.** $\theta_1 = \{x \mapsto f(y),\ y \mapsto z\}$, $\theta_2 = \{x \mapsto a,\ y \mapsto b,\ z \mapsto y\}$. What is $\theta_1\theta_2$?

**▸ Completed:**

- $x \mapsto f(y)\theta_2 = f(b)$ — keep;
- $y \mapsto z\theta_2 = y$ — identity, delete by rule 2;
- from $\theta_2$: $x \mapsto a$ and $y \mapsto b$ are deleted by rule 1 ($x,y \in \mathrm{dom}(\theta_1)$); $z \mapsto y$ survives.

$$\boxed{\theta_1\theta_2 = \{x \mapsto f(b),\ z \mapsto y\}}$$

Check: $x(\theta_1\theta_2) = f(b) = (x\theta_1)\theta_2$; $y(\theta_1\theta_2) = y = (z)\theta_2 = (y\theta_1)\theta_2$; $z(\theta_1\theta_2) = y = (z\theta_1)\theta_2$. ✓

## 6.4 Instances and ground instances

An **instance** of an expression $E$ (term, atom, literal, clause) is any $E\theta$.

- Instances of $f(x,a,g(x))$ include $f(x,a,g(x))$, $f(y,a,g(y))$, $f(a,a,g(a))$, $f(g(b),a,g(g(b)))$.
- $f(b,a,g(c))$ is **not** an instance — a substitution must replace *all* occurrences of $x$ by the same term.
- A **ground instance** is an instance containing no variables.

## 6.5 Herbrand's theorem

For a set of clauses $S$, let $S^*$ be the set of ground instances of clauses in $S$.

> **Theorem.** Let $\Sigma$ have at least one constant symbol and let $S$ be a set of (implicitly universally quantified) clauses over $\Sigma$. The following are equivalent:
> 1. $S$ is unsatisfiable;
> 2. $S^*$ is unsatisfiable;
>
> and, by compactness,
>
> 3. some **finite** subset of $S^*$ is unsatisfiable.

So unsatisfiability of arbitrary clause sets reduces to unsatisfiability of *ground* clause sets — even though $S^*$ is normally infinite. (If $\Sigma$ has no constant, add a fresh one; this changes nothing about satisfiability.)

## 6.6 Lifting

**Lifting** is a proof technique for completeness theorems:

1. prove completeness of the inference system for **ground** clauses;
2. lift the proof to the non-ground case.

### The problem it solves

Take $p(x,a) \lor q_1(x)$ and $\neg p(y,z) \lor q_2(y,z)$. With function symbols around, each has infinitely many ground instances:

$$\{\,p(r,a) \lor q_1(r) \mid r \text{ ground}\,\}, \qquad \{\,\neg p(s,t) \lor q_2(s,t) \mid s,t \text{ ground}\,\}.$$

Two ground instances resolve exactly when $r = s$ and $t = a$, giving infinitely many inferences

$$\frac{p(s,a) \lor q_1(s) \qquad \neg p(s,a) \lor q_2(s,a)}{q_1(s) \lor q_2(s,a)}\,(BR).$$

### The idea

Represent all of them by **one** non-ground inference:

$$\frac{p(x,a) \lor q_1(x) \qquad \neg p(y,z) \lor q_2(y,z)}{q_1(y) \lor q_2(y,a)}\,(BR)$$

Is this always possible? **Yes** — because $\{x \mapsto y,\ z \mapsto a\}$ solves the "equation" $p(x,a) = p(y,z)$, and every ground instance of the conclusion arises by instantiating that solution further.

## 6.7 Lifting lemma for $\mathbb{BR}$ (Robinson 1965)

To lift binary resolution with selection:

- work with non-ground clauses;
- generalise "the same ground atom" to **unifiability** of non-ground atoms;
- compute **most general unifiers only**.

> **Lifting Lemma.** Let $C$ and $D$ share no variables. If there is a ground inference
> $$\frac{C\theta_1 \qquad D\theta_2}{C'}\ (\text{ground } \mathbb{BR}),$$
> then there is a non-ground inference
> $$\frac{C \qquad D}{C''}\ (\mathbb{BR})$$
> and a substitution $\theta$ with $C' = C''\theta$.

Similar lifting lemmas hold for every inference of $\mathbb{BR}$ and of $\mathbb{S}\mathrm{up}$.

*(This lemma and the "What should we lift?" list of §6.12 are printed again, word for word, at the start of L7; they are given once here.)*

## 6.8 Unifiers and most general unifiers

A **unifier** of $s_1$ and $s_2$ is a substitution $\theta$ with $s_1\theta = s_2\theta$ — a solution of the "equation" $s_1 = s_2$. For a system $s_1 = s_1',\dots,s_n = s_n'$, a substitution solving all equations at once is a **simultaneous unifier**.

A solution $\theta$ of a set of equations $E$ is **most general** if for every solution $\tau$ there is a $\rho$ with $\theta\rho = \tau$. Same definition for a **most general unifier (mgu)**.

**Example.** Unify $f(x_1, g(x_1), x_2)$ and $f(y_1,y_2,y_2)$:

$$\theta_1 = \{y_1 \mapsto x_1,\ y_2 \mapsto g(x_1),\ x_2 \mapsto g(x_1)\}, \qquad \theta_2 = \{y_1 \mapsto a,\ y_2 \mapsto g(a),\ x_2 \mapsto g(a),\ x_1 \mapsto a\}.$$

Both unify, but only $\theta_1$ is an mgu; $\theta_2 = \theta_1\{x_1 \mapsto a\}$ is an instance of it.

## 6.9 The unification algorithm

An equation $x = t$ in $E$ is **isolated** if $x$ has exactly one occurrence in the whole of $E$.

**Input.** A finite set of equations $E$ ($s,t$ terms; $c,d$ constants; $f,g$ function symbols; $x$ a variable).
**Output.** A solution of $E$, or failure.

1. While $E$ contains a **non-isolated** equation $s = t$, inspect the pair $(s,t)$:
   - $(t,t)$ ⇒ delete this equation from $E$;
   - $(x,t)$ ⇒ if $x$ occurs in $t$, **halt with failure** (*occurs check*); otherwise replace every other occurrence of $x$ in $E$ by $t$;
   - $(t,x)$ ⇒ replace the equation by $x = t$ and proceed as in the previous case;
   - $(c,d)$ with $c \neq d$ ⇒ halt with failure;
   - $(c, f(t_1,\dots,t_n))$ or $(f(t_1,\dots,t_n), c)$ ⇒ halt with failure;
   - $(f(s_1,\dots,s_m), g(t_1,\dots,t_n))$ with $f \neq g$ ⇒ halt with failure;
   - $(f(s_1,\dots,s_n), f(t_1,\dots,t_n))$ ⇒ replace it by $\{s_1 = t_1,\dots,s_n = t_n\}$ *(decomposition)*.
2. When $E = \{x_1 = r_1,\dots,x_\ell = r_\ell\}$ with every equation isolated, return $\{x_1 \mapsto r_1,\dots,x_\ell \mapsto r_\ell\}$.

### Worked examples

**▸ Completed (the lecture lists three systems and gives no answers).**

**(a)** $\{\,h(g(f(x),a)) = h(g(y,y))\,\}$

Decompose $h$: $g(f(x),a) = g(y,y)$. Decompose $g$: $f(x) = y$ and $a = y$. Orient: $y = f(x)$, $y = a$. Now $y$ is non-isolated; substituting $y \mapsto f(x)$ into the second gives $f(x) = a$ — a clash between the function symbol $f$ and the constant $a$. **Failure: not unifiable.**

**(b)** $\{\,h(f(y),y,f(z)) = h(z, f(x), x)\,\}$

Decompose: $f(y) = z$, $y = f(x)$, $f(z) = x$. From the first, $z = f(y)$; with $y = f(x)$, $z = f(f(x))$. From the third, $x = f(z) = f(f(f(x)))$ — $x$ occurs in its own binding. **Failure: occurs check.**

**(c)** $\{\,h(g(f(x),z)) = h(g(y,y))\,\}$

Decompose: $f(x) = y$, $z = y$. Orient and propagate $y \mapsto f(x)$:

$$\boxed{\mathrm{mgu} = \{\,y \mapsto f(x),\ z \mapsto f(x)\,\}}$$

Both sides become $h(g(f(x), f(x)))$. ✓ Compare with (a): the only change is $a \rightsquigarrow z$, and a variable is willing to be $f(x)$ where the constant $a$ was not.

## 6.10 Properties

> **Theorem.** Run the algorithm on $s = t$.
> - If $s$ and $t$ are unifiable, it terminates and outputs a **most general** unifier.
> - If they are not unifiable, it terminates with failure.

We write $\mathrm{mgu}(s,t)$ for a most general unifier and $\mathrm{mgs}(E)$ for a most general solution of an equation set $E$. (Both are unique only up to renaming — see the next exercise.)

## 6.11 Exercise: the trivial systems

Consider $\varnothing$ and $\{a = a\}$. What is the set of all solutions? What is the set of most general solutions?

**▸ Completed (no answer was published).**

- **All solutions:** *every* substitution. Both systems impose no constraint — $a = a$ holds under any $\theta$.
- **Most general solutions:** exactly the **renamings** (substitutions that are bijections from variables to variables), of which the identity $\varepsilon$ is the canonical representative. For any solution $\tau$ we have $\varepsilon\tau = \tau$, so $\varepsilon$ is most general; and if $\rho$ is a renaming then $\rho(\rho^{-1}\tau) = \tau$, so $\rho$ is most general too.
- **Nothing else qualifies.** $\{x \mapsto y\}$ is *not* most general: any $\{x\mapsto y\}\rho$ assigns $x$ and $y$ the same term, so it can never yield $\tau = \{x \mapsto a,\ y \mapsto b\}$.

Moral: "the" mgu is only unique modulo renaming — which is why implementations are free to return any variant.

## 6.12 What do we lift?

- the ordering $\succ$;
- the selection function $\sigma$;
- the calculus $\mathbb{S}\mathrm{up}^{\mathrm{sat}}$.

And the reason lifting works at all: we solve equations between terms and atoms using **most general** unifiers, so one non-ground inference covers all ground instances at once.
---

# Lecture 7 — Non-Ground Superposition

## 7.1 Recap

Idea (Robinson 1965; Bachmair & Ganzinger 1990): represent an infinite number of ground inferences by a single non-ground inference. Work with non-ground clauses; generalise "same atom" to unifiability; compute mgus only. (Lifting lemma: §6.7; what gets lifted: §6.12. Both are reprinted verbatim at the start of L7 and are not repeated here.)

## 7.2 KBO, ground case (recap)

Fix $\Sigma$ with precedence $\gg$ and weight function $w:\Sigma \to \mathbb{N}$; the weight of a ground term is

$$|g(t_1,\dots,t_n)| = w(g) + \sum_{i=1}^n |t_i| .$$

$g(t_1,\dots,t_n) \succ_{\text{KB}} h(s_1,\dots,s_m)$ iff the weight is strictly greater, or the weights are equal and either $g \gg h$, or $g = h$ and the argument tuples compare lexicographically left-to-right.

**Ground admissibility.** $w(a) > 0$ for every constant; if a unary $f$ has $w(f) = 0$ then $f$ is the greatest symbol in $\gg$.

## 7.3 Weight functions, non-ground case

Extend $w$ to variables, $w : \Sigma \cup \mathrm{Vars} \to \mathbb{N}$, requiring:

- $w(x) = v_0$ for **all** variables $x$, with $v_0 > 0$;
- $w(a) \ge v_0$ for every constant $a \in \Sigma$;
- if $w(f) = 0$ for a unary $f$, then $f \gg g$ for all $g \neq f$.

Hence at most one unary function has weight $0$. For a term $s$ and variable $x$, $\#(x,s)$ denotes the number of occurrences of $x$ in $s$.

Note the constant condition **strengthens** in the non-ground case: ground admissibility asks only $w(a) > 0$, whereas here $w(a) \ge v_0$. Without it, instantiating a variable by a light constant could decrease a term's weight and break stability under substitution.

## 7.4 KBO, non-ground case

For terms $s,t$: $s \succ_{\text{KB}} t$ iff $\#(x,s) \ge \#(x,t)$ for **every** variable $x$ and

- $|s| > |t|$ *(by weight)*; **or**
- $|s| = |t|$ and one of:
  - $t = x$ and $s = f^n(x)$ for some $n \ge 1$;
  - $s = g(s_1,\dots,s_n)$, $t = h(t_1,\dots,t_m)$ and $g \gg h$ *(by precedence)*;
  - $s = g(s_1,\dots,s_n)$, $t = g(t_1,\dots,t_n)$ and for some $i$: $s_1 = t_1, \dots, s_{i-1} = t_{i-1}$ and $s_i \succ_{\text{KB}} t_i$ *(lexicographic)*.

*(Presentation note: the lecture writes the arguments of $s$ as $t_1,\dots,t_n$ and those of $t$ as $s_1,\dots,s_m$ — inherited from the ground case, where the roles of $s$ and $t$ are the other way round. The clauses are stated consistently and the definition is correct as published; the letters have simply been swapped above so that $s$'s arguments are called $s_i$.)*

**The variable-count condition is the whole difference from the ground case.** It is what makes KBO stable under substitution: if some $x$ occurred more often in $t$ than in $s$, instantiating $x$ by something huge would flip the comparison. Its practical consequence is that many pairs of non-ground terms are simply **incomparable** — e.g. $x$ and $f(c)$ — and calculus conditions must be stated as $\not\succeq$ rather than $\prec$.

## 7.5 Selection functions and lifting

> If for some grounding substitution $\theta$ the literal $L\theta$ is selected in $L\theta \lor C\theta$, then $L$ is selected in $L \lor C$.

Hence if the ground selection function is well-behaved (§2.10), so is the lifted non-ground one.

## 7.6 Non-ground superposition

$$\frac{\underline{l = r} \lor C \qquad \underline{s[l'] = t} \lor D}{(s[r] = t \lor C \lor D)\theta}\,(Sup) \qquad\qquad \frac{\underline{l = r} \lor C \qquad \underline{s[l'] \neq t} \lor D}{(s[r] \neq t \lor C \lor D)\theta}\,(Sup)$$

where

1. $\theta = \mathrm{mgu}(l, l')$;
2. $l'$ is **not a variable**;
3. $r\theta \not\succeq l\theta$;
4. $t\theta \not\succeq s[l']\theta$.

**Observations.**

- The ordering is **partial** on non-ground terms, which is why the conditions are negative ($r\theta \not\succeq l\theta$, not $l\theta \succ r\theta$).
- These conditions are checked **a posteriori** — after unification, since they mention $\theta$. But if $l \succ r$ already holds then $l\theta \succ r\theta$ for every $\theta$ (stability), which lets a prover prune many inferences **a priori**.
- Condition 2 matters: without "$l'$ is not a variable" one could rewrite at variable positions, which is both explosive and unnecessary for completeness (such inferences are covered by instances).

## 7.7 Equality resolution and equality factoring

**Equality resolution:**

$$\frac{\underline{s \neq s'} \lor C}{C\theta}\,(ER), \qquad \theta = \mathrm{mgu}(s,s')$$

**Equality factoring:**

$$\frac{\underline{l = r} \lor l' = r' \lor C}{(l = r \lor r \neq r' \lor C)\theta}\,(EF)$$

where $\theta = \mathrm{mgu}(l,l')$, $r\theta \not\succeq l\theta$, $r'\theta \not\succeq l\theta$, and $r'\theta \not\succeq r\theta$.

## 7.8 Non-ground binary resolution and factoring

$$\frac{\underline{P} \lor C_1 \qquad \underline{\neg P'} \lor C_2}{(C_1 \lor C_2)\theta}\,(BR), \qquad \theta = \mathrm{mgu}(P,P')$$

$$\frac{\underline{P} \lor \underline{P'} \lor C}{(P \lor C)\theta}\,(Fact) \qquad\qquad \frac{\underline{\neg P} \lor \underline{\neg P'} \lor C}{(\neg P \lor C)\theta}\,(Fact)$$

in both cases with $\theta = \mathrm{mgu}(P,P')$. (Positive and negative factoring respectively — note that L2's and L4's $\mathbb{BR}\sigma$ list positive factoring only; see the note in §2.5.)

**Exercise 7.A** — the refutation exercise stated in the lecture is published Exercise 7.1; see §E.7.1.

## 7.9 Checking redundancy in practice

Assume the current search space $S$ contains no redundant clauses. Then redundancy can only appear when a **new child** (the conclusion of an inference) is added, and only in two ways:

1. the **child itself** is redundant w.r.t. $S$;
2. the child makes some **existing clause** redundant.

Under a fair strategy we test for both after every inference that generates a new clause. (In some cases one can do better than testing blindly.)

*(The published section says the same thing twice in slightly different words; merged.)*

## 7.10 Subsumption (non-ground)

> **Definition.** $C$ **subsumes** $D$ if $C\theta \subseteq D$ for some substitution $\theta$.
>
> **Subsumption and redundancy.** If $S$ contains distinct clauses $C$ and $D$ with $C$ subsuming $D$, then $D$ is redundant in $S$ and may be removed.

**⚠ Read "$\subseteq$" carefully.** Whether $C\theta \subseteq D$ is *set* inclusion or *multiset* inclusion decides cases like $p(x) \lor p(y)$ vs $p(f(c))$ — see Exercise 7.2 (§E.7.2), where the published answer takes the multiset reading while the definition above states the set one. This is the same unresolved choice flagged in §1, and it also decides Exercise 2.4 (§E.2.4) — in the opposite direction.

## 7.11 Demodulation (non-ground)

$$\frac{l = r \qquad L[l'] \lor D}{L[r\theta] \lor D}\,(Dem)$$

where $l\theta = l'$ (**matching**, not unification — only the equation is instantiated), $l\theta \succ r\theta$, and $(L[l'] \lor D) \succ (l\theta = r\theta)$. Equivalently:

$$\frac{l = r \qquad L[l\theta] \lor D}{L[r\theta] \lor D}\,(Dem), \qquad l\theta \succ r\theta,\quad (L[l\theta] \lor D) \succ (l\theta = r\theta).$$

The right premise is deleted — this is a **simplifying** inference.

## 7.12 General redundancy (non-ground)

$D$ is redundant with respect to $C$ if the ground instances of $D$ are redundant with respect to the ground instances of $C$.

**▸ Fixed (notation).** The published version writes $D^*$ both for "the set of ground instances of $D$" and for "an arbitrary ground instance of $D$" inside the same sentence, which makes the sufficient condition unreadable. Stated properly:

> It suffices to find a substitution $\theta$ such that for **every** ground instance $D\tau$ of $D$:
> 1. $D\tau \succ C\theta$, and
> 2. $C\theta \models D\tau$.

## 7.13 Generating vs. simplifying inferences

An inference

$$\frac{C_1 \quad \dots \quad C_n}{C}$$

is **simplifying** if at least one premise $C_i$ becomes redundant once $C$ is added; we say $C_i$ is *simplified into* $C$. Otherwise it is **generating**.

**Note.** Deciding whether an inference is simplifying is undecidable in general (as are several related checks).

**Key principles.**

1. Apply simplifying inferences **eagerly**; apply generating inferences **lazily**.
2. Checking for simplifying inferences must pay off — in practice it must be *cheap*.

## 7.14 Redundancy-checking workflow

Whenever a new clause $C$ is added:

- **Retention test** — is $C$ itself redundant? (If so, discard it.)
- **Forward simplification** — can $C$ be simplified using existing clauses?
- **Backward simplification** — does $C$ simplify or delete older clauses?

### Examples of redundancy tests

- **Retention:** tautology checking; subsumption.
- **Simplification:** demodulation (forward and backward); **subsumption resolution**:

$$\frac{A \lor C \qquad \neg B \lor D}{D}\,(SR) \qquad\qquad \frac{\neg A \lor C \qquad B \lor D}{D}\,(SR)$$

**▸ Fixed.** The published rules carry an empty name "()" and the side condition *"whenever some substitution $\theta$ satisfies $A\theta \lor C\theta \subseteq B \lor D$"*, which does not pin down that $A\theta$ must match the *resolved* literal. The precise condition is:

> there is a substitution $\theta$ with $A\theta = B$ and $C\theta \subseteq D$.

Then $D$ follows from the two premises, and $D$ subsumes $\neg B \lor D$ — so the second premise is redundant and is **replaced** by $D$.

### Cost of the criteria

- Tautology checking is based on **congruence closure**.
- Subsumption and subsumption resolution are **NP-complete**.

### Observations

- Forward simplifications come in **chains** (a simplified clause may be simplifiable again); after such a chain, run the retention test again.
- Backward simplification is often expensive.
- In practice the retention test includes extra heuristics that may sacrifice completeness — e.g. discarding clauses that are too heavy. (This is one of the places where a real prover deliberately gives up the fairness guarantee of §3.7 in exchange for speed, and it is why scenario 3 of §3.11 reports *unknown* rather than *satisfiable*.)
---

# Part E — Exercises with worked solutions

The published solutions are reproduced in corrected form. Where the published answer is wrong, incomplete, or has premises swapped, this is flagged.

> **▸ Fixed (numbering).** Earlier versions of these notes filed the three ordering exercises as "Ex 4.1–4.3". They are in fact **Problems 3.2, 3.3 and 3.4 on the Ex-L3 page**, and are numbered accordingly below. The L4 lecture page poses the clause-comparison example (§4.4) without an answer; the answer lives on the Ex-L3 page.

## E.2.1 Infinitely many refutations of a four-clause set

**Problem.** $S = \{\neg p \lor \neg q,\ \neg p \lor q,\ p \lor \neg q,\ p \lor q\}$. Show there are infinitely many different $\mathbb{BR}$ derivations of $\square$ from $S$.

**Solution.** One refutation:

| # | Clause | From |
|---|---|---|
| (5) | $\neg q \lor \neg q$ | $BR$ on $p$: $(\neg p \lor \neg q)$, $(p \lor \neg q)$ |
| (6) | $q \lor q$ | $BR$ on $p$: $(\neg p \lor q)$, $(p \lor q)$ |
| (7) | $q$ | $Fact$ on (6) |
| (8) | $\neg q$ | $BR$: (5), (7) |
| (9) | $\square$ | $BR$: (7), (8) |

Now insert this detour any number of times before the last step:

$$q \ \xrightarrow{\ BR \text{ with } \neg p \lor \neg q\ }\ \neg p \ \xrightarrow{\ BR \text{ with } p \lor q\ }\ q$$

Each repetition yields a strictly larger derivation tree ending in $\square$, so there are infinitely many distinct refutations. $\blacksquare$

**▸ Fixed (the published last step does not close).** The published solution ends *"Resolve the second copy of $(q \lor q)$ with $\neg q$ to obtain $\square$."* Resolving $q \lor q$ against the unit $\neg q$ removes **one** copy of $q$ and yields $q$, not $\square$: binary resolution cuts a single literal pair per step. The step must instead resolve the **factored** unit $q$ (step (7) above) against $\neg q$. Written as published, the derivation is one factoring step short of closing.

**Why this matters.** It is the same point the exercise is making: an unfactored $q \lor q$ and the factored $q$ are different clauses in $\mathbb{BR}$, and conflating them is exactly what makes the derivation count infinite rather than finite.

## E.2.2 The induced literal ordering is well-founded

**Problem.** Let $\succ$ be a well-founded strict ordering on atoms. Prove the induced ordering on literals (§1) is well-founded.

**Solution.** Suppose $L_0 \succ L_1 \succ L_2 \succ \cdots$ is an infinite descending chain of literals. By the definition of $\succ_{\text{lit}}$, each step either strictly decreases the atom or keeps it fixed (and flips $\neg A$ down to $A$). So

$$\mathrm{atom}(L_0) \succeq \mathrm{atom}(L_1) \succeq \mathrm{atom}(L_2) \succeq \cdots,$$

and since $\succ$ on atoms is well-founded, the atoms are eventually constant: there is $n$ with $\mathrm{atom}(L_i) = A$ for all $i \ge n$. But only two literals have atom $A$, namely $\neg A \succ A$, so from index $n$ the chain can make at most one strict step and then has nowhere to go — contradicting infinitude. $\blacksquare$

**▸ Fixed (the published proof uses a false lemma).** The published solution asserts *"whenever $L_i \succ L_j$ we also have $\mathrm{atom}(L_i) \succ \mathrm{atom}(L_j)$"* and then transfers the chain directly to atoms. That is false for the polarity clause: $\neg p \succ p$ while $\mathrm{atom}(\neg p) = \mathrm{atom}(p)$. The correct statement uses $\succeq$, which is why the argument needs the extra observation about the two-element fibre above each atom.

**Alternative proof.** Map $L \mapsto (\mathrm{atom}(L), \mathrm{pol}(L))$ where $\mathrm{pol}(\neg A) \succ_2 \mathrm{pol}(A)$ on a two-element set. Then $\succ_{\text{lit}}$ *is* the lexicographic product $\succ \times \succ_2$, and a two-element strict ordering is trivially well-founded, so §E.3.3 applies directly.

## E.2.3 Is this selection well-behaved, and how many inferences fire?

**Problem.** $p \succ q$, and $\sigma$ selects as shown:

$$\{\ \neg p \lor \underline{\neg q},\quad \underline{\neg p} \lor q,\quad p \lor \underline{\neg q},\quad \underline{p} \lor q\ \}$$

(a) Is $\sigma$ well-behaved on $S$? (b) How many $\mathbb{BR}\sigma$-inferences are applicable to $S$?

**Solution.**

**(a) Yes.** In the first three clauses a **negative** literal is selected, which satisfies the first disjunct of §2.10 outright, whatever the ordering. In the fourth clause, $\underline{p} \lor q$, no negative literal is selected, so all maximal literals must be — and since $p \succ q$, the literal $p$ is the unique maximal one and it is selected. ✓

**(b) Exactly one.** No factoring applies: no clause contains the same positive literal twice. A $(BR)$ step needs a complementary pair of **selected** literals. The selected literals are $\neg q,\ \neg p,\ \neg q,\ p$; the only complementary pair among them is $\underline{\neg p}$ in clause 2 and $\underline{p}$ in clause 4:

$$\frac{\underline{\neg p} \lor q \qquad \underline{p} \lor q}{q \lor q}\,(BR)$$

The two occurrences of $\neg q$ have no selected $q$ to meet, because in both clauses containing $q$ the selected literal is something else. So one inference. $\blacksquare$

Note the conclusion $q \lor q$ is unfactored — a reminder that $(Fact)$ in $\mathbb{BR}\sigma$ needs **both** copies selected, which $\sigma$ has not done here.

## E.2.4 A selection that is well-behaved for no ordering

**Problem.** Give a non-tautological ground clause with at least one selected literal such that the selection is not well-behaved for any ordering.

**Solution.** Take $p \lor \underline{p}$. There is no negative literal, so well-behavedness requires that **all** maximal literals be selected. Read as a bag, the clause is $\{p, p\}$: both occurrences are maximal under every ordering, and only one is selected. No choice of $\succ$ repairs this, since the ordering never gets to separate a literal from itself. $\blacksquare$

**▸ Note (this answer depends on the bag reading).** If a clause is a **set** of literals, then $p \lor p$ *is* the clause $p$, its single literal is selected, and the selection is well-behaved — the exercise would have no answer of this shape. In fact no ground clause over *distinct* atoms works either: given distinct ground atoms one can always choose an ordering making one literal strictly maximal, and selecting that one is well-behaved. So the exercise is answerable **only** under the bag reading, which is a genuine (if unstated) commitment by the lecture.

Compare §E.7.2, where the site's answer commits to the bag reading again, but the *definition* printed alongside it commits to the set reading. The course needs both conventions and never says which is in force. See §1.

## E.2.5 A seven-clause refutation, and the silent factoring in it

**Problem.** $S = \{\neg q \lor r,\ \neg p \lor q,\ \neg r \lor \neg q,\ \neg q \lor \neg p,\ \neg p \lor \neg r,\ \neg r \lor p,\ r \lor q \lor p\}$. Prove $S$ unsatisfiable in $\mathbb{BR}$.

**Solution.** Number the clauses (1)–(7) in the order given. The lecture's own derivation is

| # | Clause | From |
|---|---|---|
| (8) | $q \lor p$ | (6), (7) |
| (9) | $q$ | (2), (8) |
| (10) | $r$ | (1), (9) |
| (11) | $\neg q$ | (3), (10) |
| (12) | $\square$ | (9), (11) |

**▸ Note (two factoring steps are omitted).** Steps (8) and (9) are labelled as resolutions but each also needs a $(Fact)$ step:

- (8): resolving $\underline{\neg r} \lor p$ against $\underline{r} \lor q \lor p$ on $r$ gives $p \lor q \lor p$ — three literals as a bag. Factoring the two copies of $p$ gives $q \lor p$.
- (9): resolving $\neg p \lor q$ against $q \lor p$ on $p$ gives $q \lor q$. Factoring gives $q$.

Steps (10)–(12) are clean single resolutions. This is the same duplicate-collapse convention flagged in §4.16 and §1: the lectures write derivations as if clauses were sets while defining them as bags. Under the set reading the derivation is exactly as printed; under the bag reading it is 7 steps, not 5.

**TPTP part.** Encode each clause as a `cnf(...)` formula and run `vampire -av off input.p`; the option switches off the AVATAR architecture so the output is a plain resolution proof ending in the empty clause.

## E.3.1 The limit of a fair inference process is the closure

**Problem.** Let $\mathbb{I}$ be a sound inference system, $S_0$ a non-empty clause set, and $S_0 \Rightarrow S_1 \Rightarrow \dots$ a fair $\mathbb{I}$-inference process with limit $S_\infty$. Show $S_\infty$ is the $\mathbb{I}$-closure of $S_0$.

**Solution.** Recall (§3.4) that in an $\mathbb{I}$-inference process no clause is ever deleted, so $S_\infty = \bigcup_i S_i$ and $S_0 \subseteq S_\infty$. Three steps.

**1. $S_\infty$ is saturated.** Suppose not: there are $C_1,\dots,C_n \in S_\infty$ and an inference $\frac{C_1 \ \cdots\ C_n}{C}$ with $C \notin S_\infty$. Each $C_i$ lies in some $S_{k_i}$ and, since nothing is deleted, in every later set. Fairness applies to inferences with all premises in $S_\infty$, so $C \in S_j$ for some $j$ — hence $C \in S_\infty$. Contradiction.

**2. Every saturated superset of $S_0$ contains $S_\infty$.** Let $X$ be $\mathbb{I}$-saturated with $S_0 \subseteq X$. By induction on $i$, $S_i \subseteq X$:

- *Base.* $S_0 \subseteq X$ by assumption.
- *Step.* Assume $S_i \subseteq X$. If $S_{i+1} = S_i$ we are done. Otherwise $S_{i+1} = S_i \cup \{C\}$ where $C$ is the conclusion of an inference with premises in $S_i$, hence in $X$; saturation of $X$ gives $C \in X$. So $S_{i+1} \subseteq X$.

Taking the union, $S_\infty \subseteq X$.

**3.** By (1) and (2), $S_\infty$ is saturated, contains $S_0$, and is contained in every saturated set containing $S_0$ — so it is the smallest such set, i.e. the $\mathbb{I}$-closure of $S_0$. $\blacksquare$

**▸ Note.** Soundness of $\mathbb{I}$ is stated in the problem but is never used: the result is purely about closure under a set of rules. Note also that this is exactly the point where fairness earns its keep — without it, step 1 fails and $S_\infty$ can be any set at all between $S_0$ and the closure.

## E.3.2 Bag ordering of two clauses sharing a maximal atom

**Problem.** Let $\succ$ be a total well-founded ordering on ground non-equality atoms, extended to literals as in §1. Let $C, D$ be ground equality-free clauses with maximal atoms $A$ and $B$. Assume $A$ and $B$ are syntactically identical, $A$ occurs **negatively** in $C$, and $A$ occurs **only positively** in $D$. Show $C \succ^{\text{bag}} D$.

**Solution.** Since $A = B$, $A$ is the maximal atom of $D$; as $A$ occurs only positively there, every other literal $L$ of $D$ satisfies

$$\neg A \ \succ\ A \ \succ\ \neg L \ \succ\ L$$

(the atom of $L$ is below $A$, and atoms dominate polarity). Hence the singleton bag $\{\neg A\}$ already dominates $D$: $\{\neg A\} \succ^{\text{bag}} D$.

In $C$, $A$ occurs negatively, so $\neg A \in C$; and for every other atom $C_i$ of $C$ we have $\neg A \succ \neg C_i \succ C_i$, so $\neg A$ is the maximal literal of $C$. Write $C = \{\neg A\} \uplus C'$. Replacing the element $\neg A$ by the literals of $D$ — all strictly smaller — is one step of the bag extension, so $C \succ^{\text{bag}} D \uplus C'$; and $D \uplus C' \succeq^{\text{bag}} D$ because removing elements makes a bag smaller (§4.3). By transitivity $C \succ^{\text{bag}} D$. $\blacksquare$

**▸ Note (two slips in the published solution).** (i) It writes *"By assumption $A$ occurs **only** negatively in $C$"*, but the hypothesis is merely that $A$ occurs negatively — $A$ may also occur positively in $C$. The proof is unaffected: all that is needed is $\neg A \in C$, and $\neg A$ is then maximal in $C$ regardless. (ii) It writes $\neg A \succ^{\text{bag}} D$, comparing a literal with a bag; this should be $\{\neg A\} \succ^{\text{bag}} D$. The step from "$\{\neg A\}$ dominates $D$" to "$C$ dominates $D$" is also left implicit, and needs the $\uplus C'$ bookkeeping above when $C$ has other literals.

**Why it matters.** This is the abstract form of the property in §4.11: the conclusion of a $(BR)$ step is strictly smaller than its rightmost premise.

## E.3.3 Lexicographic product of well-founded orderings

**Problem.** Let $\succ_1, \succ_2$ be strict well-founded orderings on $M_1, M_2$. Define on $M_1 \times M_2$:

$$(a_1,a_2) \succ^* (b_1,b_2) \iff \big(a_1 \succ_1 b_1 \ \text{ or } \ (a_1 = b_1 \text{ and } a_2 \succ_2 b_2)\big).$$

Show $\succ^*$ is well-founded.

**Solution.** Suppose $(x_0,y_0) \succ^* (x_1,y_1) \succ^* \dots$ is infinite descending. At each step the first component either strictly decreases in $\succ_1$ or stays equal. Since $\succ_1$ is well-founded, it cannot strictly decrease infinitely often, so there is $n$ with $x_i = x_{i+1}$ for all $i \ge n$. From index $n$ on, the definition forces $y_i \succ_2 y_{i+1}$ for all $i \ge n$ — an infinite $\succ_2$-descending chain, contradicting well-foundedness of $\succ_2$. $\blacksquare$

*(This is the workhorse behind KBO: weight, then precedence, then lexicographic arguments is a nested lexicographic product. It also gives the cleanest proof of §E.2.2.)*

## E.3.4 Comparing three clauses

**Problem.** With $p_6 \succ p_5 \succ p_4 \succ p_3 \succ p_2 \succ p_1$ total and well-founded, compare $p_6 \lor \neg p_6$, $\neg p_2 \lor p_4 \lor p_5$, $p_2 \lor p_3$ under the bag extension.

**Solution.**

$$p_6 \lor \neg p_6 \ \succ\ \neg p_2 \lor p_4 \lor p_5 \ \succ\ p_2 \lor p_3$$

Justification as in §4.4. The published solution reaches the same answer via the chain

$$p_6 \lor \neg p_6 \succ p_6 \succ \neg p_2 \lor p_4 \lor p_5 \succ p_5 \succ p_2 \lor p_3,$$

using the singletons $\{p_6\}$ and $\{p_5\}$ as stepping stones plus transitivity, together with the "proper superset is greater" property for the two outer steps.

**▸ Note.** The step $\{p_6\} \succ \{\neg p_2, p_4, p_5\}$ requires $p_6 \succ \neg p_2$ — a *positive* literal on a bigger atom beating a *negative* literal on a smaller one. The published solution states this instance explicitly ("$p_i \succ p_j$ and $p_i \succ \neg p_j$ for $i > j$"), and it follows from L2's definition of the induced literal ordering (§1). Earlier versions of these notes claimed the convention was never stated anywhere in the course; that claim was wrong, and is withdrawn — see §A.9.

## E.4.4 / E.5.1 Positive factoring via superposition

*(Published twice: as Exercise 4.4 and again, word for word, as Exercise 5.1.)*

**Problem.** Show that positive factoring in $\mathbb{BR}$ can be simulated by superposition inferences (ignore selection).

**Solution.** Encode non-equality atoms as equalities with $\top$ (§5.3). The factoring rule

$$\frac{p \lor p \lor C}{p \lor C}\,(Fact)$$

becomes, first by equality factoring with $s = p$, $t = t' = \top$:

$$\frac{p = \top \ \lor\ p = \top \ \lor\ C}{p = \top \ \lor\ \top \neq \top \ \lor\ C}\,(EF)$$

then by equality resolution:

$$\frac{p = \top \lor \top \neq \top \lor C}{p = \top \lor C}\,(ER)$$

which is the encoded factored clause. $\blacksquare$

## E.5.2 KBO on the group axiom $\mathrm{inverse}(\mathrm{times}(x,y)) = \mathrm{times}(\mathrm{inverse}(y),\mathrm{inverse}(x))$

**Problem.** KBO with precedence $\mathrm{inverse} \gg \mathrm{times}$. Compare the two sides when (1) $w(\mathrm{inverse}) = w(\mathrm{times}) = 1$; (2) $w(\mathrm{inverse}) = 0$, $w(\mathrm{times}) = 1$.

**Solution.** Write $L$ and $R$ for the two sides. Both contain $x$ once and $y$ once, so the variable-count condition $\#(v,\cdot) \ge \#(v,\cdot)$ holds in **both** directions and never blocks the comparison; the weights decide.

**(1)** $|L| = w(\mathrm{inverse}) + w(\mathrm{times}) + |x| + |y| = 2 + |x| + |y|$, while $|R| = w(\mathrm{times}) + 2\,w(\mathrm{inverse}) + |x| + |y| = 3 + |x| + |y|$. So

$$R \succ L: \qquad \mathrm{times}(\mathrm{inverse}(y),\mathrm{inverse}(x)) \ \succ\ \mathrm{inverse}(\mathrm{times}(x,y)).$$

**(2)** $|L| = 0 + 1 + |x| + |y| = 1 + |x| + |y| = |R| = 1 + 0 + 0 + |x| + |y|$. Weights tie, so compare top symbols: $\mathrm{inverse} \gg \mathrm{times}$, hence

$$L \succ R: \qquad \mathrm{inverse}(\mathrm{times}(x,y)) \ \succ\ \mathrm{times}(\mathrm{inverse}(y),\mathrm{inverse}(x)).$$

**Why anyone cares.** The orientation decides the direction in which this axiom is used as a rewrite rule. Case (2) — the classic choice for group theory — pushes $\mathrm{inverse}$ inwards towards the leaves and terminates; case (1) does the opposite. Setting $w(\mathrm{inverse}) = 0$ is admissible only because $\mathrm{inverse}$ is unary **and** greatest in the precedence (§5.8).

## E.5.3 Ground terms of minimal weight

**Problem.** $\Sigma$ contains only function symbols and at least one constant, with $\gg$ and $w$ admissible. Describe the ground terms of minimal weight under the induced KBO.

**Solution.** The minimal-weight ground terms are:

- the constants $c \in \Sigma$ of minimal weight among all constants; and
- the terms $f^n(c)$, $n > 0$, where $c$ is such a minimal-weight constant and $f$ is the (unique, if it exists) unary function symbol with $w(f) = 0$.

Every other ground term is built with at least one symbol of positive weight on top of at least one constant, so it weighs strictly more. Note the second family is infinite yet still linearly ordered by KBO: $f^{n+1}(c) \succ f^{n}(c)$ is settled by precedence, not by weight, which is exactly the case admissibility was designed to keep well-founded.

## E.5.4 Saturating a four-clause set under two different KBOs

**Problem.** Show $S = \{(1),(2),(3),(4)\}$ unsatisfiable by saturation with $\mathbb{S}\mathrm{up}_{\succ,\sigma}$ (including ground binary resolution) for well-behaved $\sigma$, where

$$\begin{aligned}
(1)\ & g(f(a)) = a \lor g(f(b)) = a\\
(2)\ & f(a) = a\\
(3)\ & f(b) \neq f(b) \lor f(b) = a\\
(4)\ & g(a) \neq a
\end{aligned}$$

under **(i)** $f \gg a \gg g \gg b$ with $w(f)=0, w(a)=2, w(g)=3, w(b)=1$; and **(ii)** $g \gg a \gg b \gg f$ with $w(g)=0, w(a)=3, w(f)=1, w(b)=1$. State selected literals and maximal terms.

**Solution — ordering (i).** Both weight functions are admissible: in (i) the weight-0 symbol $f$ is unary and greatest in $\gg$; in (ii) the weight-0 symbol $g$ is unary and greatest.

Weights: $|a| = 2$, $|b| = 1$, $|f(a)| = 2$, $|f(b)| = 1$, $|g(a)| = 5$, $|g(f(a))| = 5$, $|g(f(b))| = 4$.
Orientations: $f(a) \succ a$ (equal weights, $f \gg a$); $f(b) \succ b$; $g(a) \succ a$ ($5 > 2$); $g(f(a)) \succ g(f(b))$ ($5 > 4$).

Selected literals underlined, maximal terms doubly underlined:

$$\begin{aligned}
(1)\ & \underline{\underline{\underline{g(f(a))}} = a} \lor g(f(b)) = a && \text{(positive clause: the strictly maximal literal is selected)}\\
(2)\ & \underline{f(a) = a}\\
(3)\ & \underline{f(b) \neq f(b)} \lor f(b) = a && \text{(a negative literal is selected — well-behaved)}\\
(4)\ & \underline{g(a) \neq a}
\end{aligned}$$

| # | Clause | Inference |
|---|---|---|
| (5) | $f(b) = a$ | $ER$ on (3) |
| (6) | $g(a) = a \lor g(f(b)) = a$ | $Sup$: (2) into (1), rewriting $f(a) \to a$ inside $g(f(a))$ |
| (7) | $g(f(b)) = a$ | (6) with (4) |
| (8) | $g(f(b)) \neq a$ | $Sup$: **(5) into (4)** |
| (9) | $\square$ | (7) with (8) |

**▸ Fixed (premises swapped).** The published solution says *"Superposition of (4) into (5) yields (8)"*. Superposition uses a **positive** equation as its left premise and rewrites inside the right premise, so the correct reading is **(5) into (4)**: the unit equation (5) rewrites a subterm of the disequality (4). And there is a subtlety worth spelling out: since $|a| = 2 > 1 = |f(b)|$, clause (5) is oriented **$a \succ f(b)$** — it rewrites $a \to f(b)$, i.e. *right to left* as printed. Applying it to $g(a) \neq a$ at the occurrence inside $g(\cdot)$ gives $g(f(b)) \neq a$. Conditions: $a \succ f(b)$ ✓ and $g(a) \succ a$ ✓.

**▸ Note (steps (7) and (9)).** These are described as "resolving". Binary resolution on *equality* literals is not a superposition rule; it is available here only because the exercise explicitly admits ground $\mathbb{BR}$. In pure $\mathbb{S}\mathrm{up}$ each of these is $Sup$ followed by $ER$ — e.g. (6) into (4) gives $a \neq a \lor g(f(b)) = a$, then $ER$ gives (7). That variant costs two extra clauses.

**Solution — ordering (ii).** **▸ Completed.** The published answer says only *"the same comparisons hold, so the derivation repeats"*, which asserts without checking. It does hold, but for different arithmetic reasons — here are the numbers:

$$|a| = 3,\quad |b| = 1,\quad |f(a)| = 4,\quad |f(b)| = 2,\quad |g(a)| = 3,\quad |g(f(a))| = 4,\quad |g(f(b))| = 2 .$$

- $f(a) \succ a$: $4 > 3$ by weight *(in (i) this was a precedence tie-break — different reason, same result)*.
- $g(f(a)) \succ g(f(b))$: $4 > 2$, so (1) has the same maximal literal.
- $g(a) \succ a$: weights tie at $3$, broken by $g \gg a$.
- $a \succ f(b)$: $3 > 2$, so (5) again rewrites $a \to f(b)$.
- In (6), $g(a) = a$ is again strictly maximal: $|g(a)| = 3 > 2 = |g(f(b))|$.

Every condition used in the derivation therefore still holds, and (5)–(9) go through unchanged. $\blacksquare$

## E.5.5 Refutation in exactly four new clauses

**Problem.** KBO with $f \gg a \gg b \gg c$ and $w(f) = w(a) = w(b) = w(c) = 1$. Show

$$(1)\ a = b \lor a = c, \qquad (2)\ f(a) \neq f(b), \qquad (3)\ b = c$$

unsatisfiable, generating only **four** new clauses.

**Solution.** All constants weigh 1, so they are ordered purely by precedence: $a \succ b \succ c$; and $f(a) \succ f(b)$ (equal weights, same top symbol, lexicographic on $a \succ b$).

$$\begin{aligned}
(1)\ & \underline{\underline{\underline{a}} = b} \lor a = c && \{a,b\} \succ^{\text{bag}} \{a,c\} \text{ since } b \succ c\\
(2)\ & \underline{\underline{\underline{f(a)}} \neq f(b)}\\
(3)\ & \underline{\underline{\underline{b}} = c}
\end{aligned}$$

| # | Clause | Inference |
|---|---|---|
| (4) | $a = b \lor b \neq c$ | $EF$ on (1) with $s=a,\ t=b,\ t'=c$; side condition $a \succ b \succeq c$ ✓ |
| (5) | $a = b$ | (3) with (4) — resolving the equality atom $b = c$ |
| (6) | $f(b) \neq f(b)$ | $Sup$: **(5) into (2)**, rewriting $a \to b$ (valid since $a \succ b$) |
| (7) | $\square$ | $ER$ on (6) |

Exactly four new clauses, (4)–(7). $\blacksquare$

**▸ Fixed (premises swapped).** The published step 3 reads *"superposition of (2) with (5)"*; the positive unit equation (5) is the left premise and (2) is rewritten, so it is **(5) into (2)**.

**▸ Note.** Step (5) again uses binary resolution on equality literals (allowed by the exercise). In pure $\mathbb{S}\mathrm{up}$ it would be $Sup$ of (3) into (4) giving $a = b \lor c \neq c$, then $ER$ — which produces **five** new clauses and misses the challenge target. So the four-clause bound genuinely depends on $\mathbb{BR}$ being in the calculus.

## E.6.1 Unification

**Problem.** Compute the mgu, or explain failure.

1. $p(a,f(y),y)$ and $p(a,x,f(x))$
2. $p(f(x,y),f(y,z))$ and $p(z,f(w,f(y,w)))$

**Solution.**

**(1)** Decomposing gives $a = a$ (deleted), $f(y) = x$, and $y = f(x)$. Orienting the second, $x = f(y)$; substituting into the third, $y = f(f(y))$. **Occurs check fails — not unifiable.**

**(2)** Decomposing: $f(x,y) = z$ and $f(y,z) = f(w,f(y,w))$. The second decomposes further to $y = w$ and $z = f(y,w)$. Combining $z = f(x,y)$ with $z = f(y,w)$ gives $x = y$ and $y = w$. Propagating $y \mapsto w$:

$$\boxed{\mathrm{mgu} = \{\,x \mapsto w,\ y \mapsto w,\ z \mapsto f(w,w)\,\}}$$

Check: both atoms become $p(f(w,w),\, f(w,f(w,w)))$. ✓

## E.7.1 A non-ground $\mathbb{BR}$ refutation

**Problem.** Refute, in non-ground $\mathbb{BR}$, stating premises, rule, and mgu for each derived clause:

$$\begin{aligned}
(1)\ & \neg p(z,a) \lor \neg p(z,x) \lor \neg p(x,z)\\
(2)\ & p(y,a) \lor p(y,f(y))\\
(3)\ & p(w,a) \lor p(f(w),w)
\end{aligned}$$

**Solution.**

| # | Clause | Premises | Rule | mgu |
|---|---|---|---|---|
| (4) | $\neg p(z,a) \lor \neg p(a,z)$ | (1) | negative factoring of $\neg p(z,a)$ and $\neg p(z,x)$ | $\{x \mapsto a\}$ |
| (5) | $\neg p(a,a)$ | (4) | negative factoring of $\neg p(z,a)$ and $\neg p(a,z)$ | $\{z \mapsto a\}$ |
| (6) | $p(a,f(a))$ | (5), (2) | $BR$ on $p(y,a)$ / $\neg p(a,a)$ | $\{y \mapsto a\}$ |
| (7) | $\neg p(f(a),a)$ | (4), (6) | $BR$ on $\neg p(a,z)$ / $p(a,f(a))$ | $\{z \mapsto f(a)\}$ |
| (8) | $p(a,a)$ | (3), (7) | $BR$ on $p(f(w),w)$ / $\neg p(f(a),a)$ | $\{w \mapsto a\}$ |
| (9) | $\square$ | (5), (8) | $BR$ | $\varepsilon$ |

Since $\square$ is derived, the set is unsatisfiable. ✓ *(Verified: this published solution is correct as it stands — every mgu and every conclusion checks out.)*

Note how factoring does the real work: clauses (2) and (3) each say "either the second argument is $a$, or $p$ relates $y$ and $f(y)$", and (1) forbids the diagonal — two factoring steps collapse (1) to the single unit $\neg p(a,a)$, after which the refutation is mechanical. Note also that both factoring steps are **negative**, so this exercise silently uses the $L7$ version of the calculus (§7.8), not the positive-factoring-only $\mathbb{BR}\sigma$ of L2/L4.

## E.7.2 Subsumption — the one that needs correcting

**Problem.** $p$ a unary predicate, $f$ a unary function, $x,y$ variables, $c$ a constant. Let $C_1 = p(x) \lor p(y)$, $C_2 = p(x)$, $D = p(f(c))$.
(a) Does $C_1$ subsume $D$? (b) Does $C_2$ subsume $D$?

**(b) Yes.** $\theta = \{x \mapsto f(c)\}$ gives $C_2\theta = p(f(c)) = D$. *(The published answer agrees.)*

**(a) It depends on a convention the lecture never fixes — and the published answer "No" contradicts the definition printed alongside it.**

The definition is: $C$ subsumes $D$ iff $C\theta \subseteq D$ for some $\theta$. Take $\theta = \{x \mapsto f(c),\ y \mapsto f(c)\}$. Then

$$C_1\theta = p(f(c)) \lor p(f(c)) .$$

If a clause is a **set** of literals — which is what the symbol "$\subseteq$" means as written — this *is* the clause $p(f(c))$, so $C_1\theta \subseteq D$ and $C_1$ subsumes $D$: the answer is **Yes**.

The published justification (*"any instance of $C_1$ contains two literals, whereas $D$ has only one"*) is the **multiset** reading: as a multiset, $\{p(f(c)), p(f(c))\} \not\subseteq \{p(f(c))\}$, giving **No**.

| Clauses read as | Does $p(x) \lor p(y)$ subsume $p(f(c))$? |
|---|---|
| **sets** of literals (the definition as printed in L7) | **Yes**, via $\{x \mapsto f(c),\ y \mapsto f(c)\}$ |
| **multisets** of literals (the published answer, and L4's "clauses are bags") | **No** |

**Which is standard.** The set reading is the usual one: $\theta$-subsumption in the resolution literature allows several literals of $C$ to be matched onto one literal of $D$, and the redundancy criterion stays sound under it, because $C_1 \models D$ genuinely holds here — instantiate both variables to $f(c)$ and the clause $\forall x \forall y\,(p(x) \lor p(y))$ forces $p(f(c))$. So deleting $D$ loses nothing.

**▸ Fixed (a wrong argument in earlier versions of these notes).** An earlier draft argued that the set reading must be intended *because otherwise the NP-completeness claim of §7.14 would be unmotivated*. That reasoning does not hold: $\theta$-subsumption is NP-complete under **both** readings — requiring the literal map to be injective does not make the search tractable. The NP-completeness of subsumption therefore does not decide the question, and the argument has been withdrawn. What remains, and is enough, is that the lecture states the set definition and then answers its own exercise under the multiset one.

**Cross-reference.** Exercise 2.4 (§E.2.4) pushes the other way: it is answerable *only* under the multiset reading. The course genuinely needs both conventions in different places, which is precisely why one of them should have been stated.

## E.7.3 A superposition refutation with a "no mixing" constraint

**Problem.** $x$ a variable, $a,b,c$ constants, $f$ unary. Give a **superposition-only** refutation (no $\mathbb{BR}$) of

$$\{\ x = f(c),\qquad a \neq b\ \}$$

such that no derived clause mixes the symbols $\{f,c\}$ with $\{a,b\}$. Name each derived clause, cite premises, record the mgu.

**Why the set is unsatisfiable.** $x = f(c)$ is universally quantified: *everything* equals $f(c)$, so the domain is a singleton and $a = b$ — contradicting $a \neq b$.

**Solution.**

| # | Clause | Premises | Rule | mgu |
|---|---|---|---|---|
| (1) | $f(c) = x$ | — | axiom (sides swapped; an equality is a multiset of its two terms, §4.12) | — |
| (2) | $a \neq b$ | — | axiom | — |
| (3) | $x = y$ | (1), (1)′ | $Sup$ of (1) into a renamed copy $f(c) = y$, rewriting $f(c) \to x$ | $\varepsilon$ |
| (4) | $a \neq x$ | (3), (2) | $Sup$ of (3) into (2), rewriting $b \to x$ | $\{y \mapsto b\}$ |
| (5) | $\square$ | (4) | $ER$ | $\{x \mapsto a\}$ |

**Points the published solution leaves implicit (▸ Completed).**

1. **Renaming apart is essential** at step (3): the two premises are $f(c) = x$ and its variant $f(c) = y$. Without renaming, "superposing (1) with itself" would be superposition of a clause with itself on the same variable and would not yield $x = y$.
2. **Why the ordering conditions do not block anything.** In $x = f(c)$ the two sides are $\succ$-**incomparable** under KBO: $f(c) \succ x$ fails the variable-count condition ($\#(x,f(c)) = 0 < 1$), and $x \succ f(c)$ fails because a variable is never above a ground term. The condition $r\theta \not\succeq l\theta$ is therefore satisfied *in both directions*, so either side may serve as the rewriting side — which is what makes step (3) legal.
3. **Why the detour through (3) is needed.** The direct route — superposing (1) into (2) — would unify the left-hand side $x$ with the subterm $b$ and produce $a \neq f(c)$, a clause mixing $\{a\}$ with $\{f,c\}$ and thus forbidden by the exercise. Deriving the "collapse" clause $x = y$ first keeps the two symbol groups apart: (3) contains no constants at all, and (4) contains only $a$.
4. **Note on rule side conditions.** Step (4) rewrites the constant $b$, which is not a variable, so the "$l'$ is not a variable" condition of §7.6 is respected. Whether $a \succ b$ or $b \succ a$ is left free; if $a \succ b$ the check $t\theta \not\succeq s[l']\theta$ is satisfied by rewriting the $b$ side, as done above.
---

# Appendix A — Errata

Every item below was checked against the live pages. Items marked ★ are new in this revision.

## A.1 Lecture 2 ★

| # | Where | Issue | Correction |
|---|---|---|---|
| 2a | Binary resolution vs. $\mathbb{BR}\sigma$ | plain $\mathbb{BR}$ factors an arbitrary literal $L$; $\mathbb{BR}\sigma$ factors only positive literals; L7 lists positive **and** negative factoring | the three systems differ; flagged in §2.5 rather than harmonised |
| 2b | Incompleteness example | the refutation given is labelled as five resolution steps, but steps (8) and (9) each also require a $(Fact)$ step | spelled out in §E.2.5 |
| 2c | Literal orderings | "Example: given $p_6 \succ \dots \succ p_1$, what is the extended ordering on literals?" — posed, never answered | answered in §1 |
| 2d | Selection functions | "a selection function does not have to be a function" — potentially confusing | kept, with the explanation that it may depend on a clause's derivation (§2.7) |

## A.2 Lecture 3 ★

| # | Where | Issue | Correction |
|---|---|---|---|
| 3a | Limit of a process | $S_\infty = \bigcup_i S_i$ here, but $\bigcup_i \bigcap_{j\ge i} S_j$ in L4 — the same symbol for two different sets, with no warning | both given, with the reconciliation, in §3.6 |
| 3b | "Limit of a Fair Inference Process" | the exercise assumes $\mathbb{I}$ is **sound**; soundness is never used | noted in §E.3.1 |
| 3c | Saturation algorithm (theory) | scenario 3 concludes "satisfiable" — true only because the process is assumed fair and the calculus complete; neither is restated | qualification added (§3.11) |
| 3d | Given-clause section | body is a bare list of four phrases ("children / given clause / candidate clauses / search space") — evidently a slide whose diagram did not survive | reconstructed as prose (§3.10) |
| 3e | Whole page | opens with two sections copied from L2 and closes with the two sections L4 opens with | deduplicated (§3, §4.1–4.2) |

## A.3 Lecture 4

| # | Where | Issue | Correction |
|---|---|---|---|
| 4a | "Problem" | `prove thatcompleteness` | *that completeness* |
| 4b | Bag extension | `replace an element byany finite number` | *by any* |
| 4c | Clause orderings | `For simpicity` | *For simplicity* |
| 4d | Redundant clauses can be removed | `consider later)redundant clauses` | missing space |
| 4e | Binary resolution with selection | `strictly smaller that the rightmost premise` | *than* |
| 4f | FOL with equality | "the order of **literals** in equalities does not matter" | the order of the two **terms/sides** of an equality; the following clause already says this correctly |
| 4g | Saturation & satisfiability | "if we built a set saturated up to redundancy, then $S_0$ is satisfiable" | add **"not containing $\square$"** — otherwise the claim is false |
| 4h | same | "a powerful way of checking **redundancy**" | checking **satisfiability** |
| 4i | same | "no obvious way to build a model of $S_0$ out of a saturated set" | needs qualifying: the completeness proof *does* construct a (possibly infinite) candidate model |
| 4j | Redundancy examples | "all non-empty other clauses in $S$ are redundant" | *all other clauses* (they are necessarily non-empty) |
| 4k | Example after $Sup$ rules | clause set given with **no task and no answer** | task + full refutation supplied (§4.16) |
| 4l | Clause-ordering example | comparison exercise posed, never answered on the lecture page | answered (§4.4); the answer is on the Ex-L3 page (§E.3.4) |
| 4m ★ | §4.16 refutation | step (5) requires collapsing a duplicated literal, which contradicts "a clause is a bag" fixed three sections earlier | flagged with the missing factoring step (§4.16) |
| 4n | Whole page | plain-text rendering shows every `≠` as `=` | see §0 |
| 4o | §4.15–4.17 | reproduced verbatim at the start of L5 | deduplicated |

## A.4 Lecture 5

| # | Where | Issue | Correction |
|---|---|---|---|
| 5a | Atom/literal orderings on equalities | only positive-vs-positive and negative-vs-negative are defined; **positive vs negative is missing**, so the "ordering on literals" is not total | added the standard encoding $s=t \mapsto \{\{s\},\{t\}\}$, $s \neq t \mapsto \{\{s,t\}\}$, giving $(s \neq t) \succ (s = t)$ (§5.1) |
| 5b | $Sup$ condition 4 | `any literal inD.` | *in D* |
| 5c | "Exercise" after BR-as-Sup | stated as a fact, not a task | *Show that…* |
| 5d | Term algebra | $\stackrel{\text{def}}{\Leftrightarrow}$ used for term definitions; $c$ in prose vs $C$ in the display | $\stackrel{\text{def}}{=}$; consistent $c$ |
| 5e | Simplification ordering | $\succ$ denotes both the precedence on symbols and the ordering on terms | precedence written $\gg$ throughout |
| 5f | KBO example | $w(g)=0$ for unary $g$ requires $g$ greatest in $\gg$ — never stated; $f$ appears as binary here, unary elsewhere | note added (§5.8) |
| 5g | KBO sections | "Ground Case" and "Ground Case: Summary" are near-verbatim duplicates (the second appends the admissibility note) | merged (§5.8) |
| 5h | Last exercise | "the set $S$ of ground **formulas**" | ground **clauses** |
| 5i | General property example | "both … are redundant" without saying redundant *with respect to what* | w.r.t. a set containing $f(a) = a$ (§5.6) |
| 5j | Exercise $\{f(a)=a, f^3(a) \neq a\}$ | no solution published | supplied (§5.6) |

## A.5 Lecture 6

| # | Where | Issue | Correction |
|---|---|---|---|
| 6a | FOL warm-up quiz | six statements, no answers | answered with justification (§6.1) |
| 6b | Substitution example ($E\theta$) | posed, not answered | $p(b,x,f(a))$ (§6.2) |
| 6c | Composition example | posed, not answered | $\{x \mapsto f(b),\ z \mapsto y\}$ (§6.3) |
| 6d | Unification examples (three systems) | posed, not answered | all three solved (§6.9) |
| 6e | Exercise $\varnothing$ / $\{a=a\}$ | posed, not answered | all substitutions; mgs = the renamings (§6.11) |
| 6f ★ | Unification algorithm | the clash case is written `(c,d) ⇒ halt with failure` with **no side condition $c \neq d$**; read literally the algorithm may fail on $\{a = a\}$ — contradicting the answer to its own exercise two sections later | side condition $c \neq d$ restored (§6.9) |
| 6g | Lifting Example / Lifting Idea / Yes! | the ground inference is displayed twice and the non-ground inference twice, across three consecutive sections | deduplicated (§6.6) |
| 6h ★ | "What Should We Lift?" / "Revisiting the Ingredients of Lifting" | the same three-item list appears **twice on this page**, and a third time at the top of L7 | given once (§6.12) |
| 6i | $\sigma$ | used for substitutions here (including in the mgu definition and the lifting lemma), for selection functions in L2–L5 | $\theta,\tau,\rho$ for substitutions throughout |

## A.6 Lecture 7

| # | Where | Issue | Correction |
|---|---|---|---|
| 7a | Non-ground $Sup$ | `t\theta \not\succeq s[l']\theta.Observations.` — heading glued to the formula | separated |
| 7b | Non-ground $\mathbb{BR}$ | `(BR),where θ is an mgu` — glued text, three occurrences | separated |
| 7c | Checking Redundancy | the same instruction is given twice in different words | merged (§7.9) |
| 7d | General Redundancy | $D^*$ used for both "set of ground instances" and "a ground instance" | restated with $D\tau$ (§7.12) |
| 7e | Subsumption resolution | rule label is empty `()`; side condition "$A\theta \lor C\theta \subseteq B \lor D$" does not force $A\theta$ to be the resolved literal | labelled $(SR)$; condition $A\theta = B$ and $C\theta \subseteq D$ (§7.14) |
| 7f | KBO non-ground | arguments of $s$ are named $t_i$ and arguments of $t$ are named $s_i$ — confusing, but **the clauses are internally consistent and the definition is correct** | letters swapped for readability only; no mathematical change (§7.4) |
| 7g | Subsumption | "$C\theta \subseteq D$" — set or multiset inclusion is never said, and the choice changes the answer to Exercise 7.2 | flagged (§1, §7.10) |
| 7h ★ | Weight functions, non-ground | the constant condition silently strengthens from $w(a) > 0$ (ground) to $w(a) \ge v_0$; no comment | reason given (§7.3) |

## A.7 Exercise pages

| # | Where | Issue | Correction |
|---|---|---|---|
| X1 ★ | **Ex 2.1**, final step | "Resolve the second copy of $(q \lor q)$ with $\neg q$ to obtain $\square$" — this yields $q$, not $\square$; binary resolution cuts one literal pair per step | resolve the **factored** unit $q$ with $\neg q$ (§E.2.1) |
| X2 ★ | **Ex 2.2** | the proof rests on "$L_i \succ L_j$ implies $\mathrm{atom}(L_i) \succ \mathrm{atom}(L_j)$", which is false for $\neg p \succ p$ | corrected proof via $\succeq$ plus the two-element fibre, or via Ex 3.3 (§E.2.2) |
| X3 ★ | **Ex 2.4** | the answer $p \lor \underline{p}$ works only if clauses are multisets; the exercise has no solution of this shape under the set reading | dependence made explicit (§E.2.4) |
| X4 ★ | **Ex 3.2** | solution says "$A$ occurs **only** negatively in $C$" but the hypothesis is merely "negatively"; also writes $\neg A \succ^{\text{bag}} D$, comparing a literal to a bag, and skips the step from $\{\neg A\}$ to $C$ | restated (§E.3.2) |
| X5 | Ex 5.4, step (8) | "Superposition of **(4) into (5)**" — premises reversed | **(5) into (4)**; also note (5) is oriented $a \succ f(b)$, so it rewrites $a \to f(b)$ (§E.5.4) |
| X6 | Ex 5.4, part 2 | "the same comparisons hold" — asserted, never checked | all weights computed for ordering (ii) (§E.5.4) |
| X7 | Ex 5.4, steps (7),(9) | "resolving" two equality literals is not a $\mathbb{S}\mathrm{up}$ rule | legal only because ground $\mathbb{BR}$ is included; pure-$Sup$ variant given |
| X8 | Ex 5.5, step 3 | "Superposition of **(2) with (5)**" — premises reversed | **(5) into (2)** |
| X9 | Ex 5.5 | the four-clause bound silently depends on $\mathbb{BR}$ being available | noted (§E.5.5) |
| X10 | **Ex 7.2(a)** | answer given as **"No"**, contradicting the lecture's own definition $C\theta \subseteq D$ under the set reading | **Yes** via $\{x \mapsto f(c),\ y \mapsto f(c)\}$; "No" holds only for multiset subsumption. Full discussion in §E.7.2 |
| X11 | Ex 7.3 | renaming apart, the incomparability of $x$ and $f(c)$, and the reason for the detour via $x=y$ are all left implicit | spelled out (§E.7.3) |
| X12 | Ex 4.4 vs Ex 5.1 | identical problem and solution published twice | merged (§E.4.4) |
| X13 | Ex 5.2 | correct, but the variable-occurrence side condition is never checked | checked (§E.5.2) |
| X14 ★ | **Ex 7.1** | the solution uses **negative** factoring twice, a rule absent from the $\mathbb{BR}\sigma$ of L2/L4 and present only in L7's system | noted (§E.7.1) |

## A.8 Cross-lecture duplication ★

Independently of any error, the same material is printed on more than one page. Consolidated here as shown:

| Material | Appears on | Given once in |
|---|---|---|
| Soundness of $\mathbb{BR}$; "can this check (un)satisfiability?" | L2, L3 | §2.6, §3.1 |
| Subsumption & tautology deletion; "Problem" | L3, L4 | §4.1–§4.2 |
| Simple ground superposition; "efficient theorem proving?" | L4, L5 | §4.15, §4.17 |
| KBO ground case | L5 (twice), L7 | §5.8, recap §7.2 |
| Lifting lemma; "what should we lift?" | L6 (list twice), L7 | §6.7, §6.12 |
| The lifting example inferences | L6, three consecutive sections | §6.6 |

## A.9 Corrections to earlier versions of these notes ★

Three claims made in the L4–L7-only version of this document were themselves wrong, and are withdrawn.

| Claim previously made | Status | Why |
|---|---|---|
| "The literal ordering convention (atoms first, polarity second) is never stated; without it the comparison $p_6 \succ \neg p_2$ cannot be justified." | **Withdrawn** | L2 states it explicitly ("if $p \succ q$ then $p \succ \neg q$ and $\neg p \succ q$; $\neg p \succ p$"), and the published solution to Ex 3.4 states the instance needed. Starting the notes at L4 hid the definition. |
| "Exercise 7.2's set reading must be intended, because otherwise §7.14's NP-completeness claim would be unmotivated." | **Withdrawn** | $\theta$-subsumption is NP-complete under both the set and the multiset reading; injectivity of the literal map does not make it tractable. The argument proves nothing. What survives is the narrower point that the lecture states one definition and answers under the other. |
| "In L7's non-ground KBO the argument naming makes the lexicographic clause read backwards." | **Corrected to a presentation note** | The naming is confusing but the clauses are internally consistent and the definition is correct as published. Only the letters were changed here. |

Two further gaps in the earlier version — no definition of a *well-behaved selection function*, and no account of *saturation, fairness, or the given-clause algorithm* — were caused by the same omission of L2 and L3, and are filled in §2.10 and §3.

---

# Appendix B — One-page rule reference

### Binary resolution with selection $\mathbb{BR}\sigma$ (ground; L2, L4)

$$\frac{\underline{p} \lor C_1 \quad \underline{\neg p} \lor C_2}{C_1 \lor C_2}\,(BR) \qquad \frac{\underline{p} \lor \underline{p} \lor C}{p \lor C}\,(Fact)$$

Positive factoring only. (Plain $\mathbb{BR}$ without selection, as first defined in L2, factors an arbitrary literal $L$.)

### Ground superposition $\mathbb{S}\mathrm{up}_{\succ,\sigma}$

$$\frac{\underline{l = r} \lor C \quad \underline{s[l] \bowtie t} \lor D}{s[r] \bowtie t \lor C \lor D}\,(Sup) \qquad \frac{\underline{s \neq s} \lor C}{C}\,(ER) \qquad \frac{\underline{s = t} \lor s = t' \lor C}{s = t \lor t \neq t' \lor C}\,(EF)$$

$\bowtie \in \{=,\neq\}$. Conditions: $l \succ r$; $s[l] \succ t$; $l=r$ strictly greater than every literal of $C$; for $Sup$-right, $s[l]=t$ $\succeq$ every literal of $D$. For $EF$: $s \succ t \succeq t'$ and $s=t$ strictly greater than every literal of $C$.

### Non-ground superposition

$$\frac{\underline{l = r} \lor C \quad \underline{s[l'] \bowtie t} \lor D}{(s[r] \bowtie t \lor C \lor D)\theta}\,(Sup) \qquad \frac{\underline{s \neq s'} \lor C}{C\theta}\,(ER) \qquad \frac{\underline{l = r} \lor l'=r' \lor C}{(l = r \lor r \neq r' \lor C)\theta}\,(EF)$$

$\theta = \mathrm{mgu}$; $l'$ not a variable; $r\theta \not\succeq l\theta$; $t\theta \not\succeq s[l']\theta$. $EF$ also needs $r'\theta \not\succeq l\theta$ and $r'\theta \not\succeq r\theta$.

### Non-ground resolution and factoring (L7)

$$\frac{\underline{P} \lor C_1 \quad \underline{\neg P'} \lor C_2}{(C_1 \lor C_2)\theta}\,(BR) \qquad \frac{\underline{P} \lor \underline{P'} \lor C}{(P \lor C)\theta}\,(Fact) \qquad \frac{\underline{\neg P} \lor \underline{\neg P'} \lor C}{(\neg P \lor C)\theta}\,(Fact)$$

L7 lists both positive and negative factoring; L2/L4 list positive only (§2.5).

### Simplification

$$\frac{l = r \quad L[l\theta] \lor D}{L[r\theta] \lor D}\,(Dem) \qquad \frac{A \lor C \quad \neg B \lor D}{D}\,(SR)$$

$Dem$: $l\theta \succ r\theta$ and $(L[l\theta] \lor D) \succ (l\theta = r\theta)$; the right premise is **deleted**.
$SR$: $A\theta = B$ and $C\theta \subseteq D$; the second premise is **replaced** by $D$.

### Search: the framework in one table

| Notion | Definition |
|---|---|
| selection function | picks ≥1 literal in every non-empty clause |
| **well-behaved** selection | in every clause: a negative literal is selected, **or** all maximal literals are |
| $\mathbb{I}$-saturated | every inference from $S$ has its conclusion in $S$ |
| $\mathbb{I}$-closure | smallest saturated superset of $S$ |
| persistent clause | $\exists i\,\forall j \ge i\ (C \in S_j)$ |
| limit $S_\infty$ | $\bigcup_i S_i$ without deletion (L3); $\bigcup_i \bigcap_{j\ge i} S_j$ with deletion (L4) |
| **fair** process | every inference with all premises in $S_\infty$ has its conclusion in some $S_i$ |
| active / passive | selected clauses that take part in inferences / those still waiting |

### Redundancy at a glance

| Notion | Definition |
|---|---|
| $C$ redundant in $S$ | $S_{\prec C} \models C$ |
| $S$ saturated up to redundancy | every inference from $S$ has its conclusion in $S$ or redundant w.r.t. $S$ |
| refutational completeness | $S$ saturated up to redundancy is unsatisfiable **iff** $\square \in S$ |
| $C$ subsumes $D$ | $C\theta \subseteq D$ for some $\theta$ (⇒ $D$ redundant) — set or multiset $\subseteq$? see §7.10 |
| simplifying inference | some premise becomes redundant once the conclusion is added |
| retention / forward / backward | is the child redundant? / can it be simplified? / does it simplify others? |

### KBO in three lines

1. Compare variable counts: $\#(x,s) \ge \#(x,t)$ for all $x$, else incomparable.
2. Compare weights: $|s| > |t|$ ⇒ $s \succ t$.
3. On a tie: $t=x$ and $s = f^n(x)$; else precedence of top symbols; else lexicographic on arguments.

Admissible weights: $w(a) \ge v_0 > 0$ for constants, $w(x) = v_0$ for variables, and at most one unary symbol may have weight $0$ — which must then be greatest in $\gg$.
