# Transcript
## Title
"When Agda met Vampire" 是一篇2026年的 preprint 的 paper。
這篇論文主要貢獻是提供 Agda 和 Vampire 之間的轉換。
而我的 Thesis Proposal 是從這篇轉換去做延伸。
## Background
- ATP
- ITP
- Vampire 的歷史與獎項
- ATP 和 ITP 的結合
- 接下來看論文主要的架構
## Motivation
- Tactics:
    Lean4 有強大的 grind tactic, Coq 有強大的 CoqHammer, Isebelle 有強大的 Sledgehammer, 但 Agda 缺乏強大的 auto tactic。
- 可以來看看一個麻煩的例子。
## Example 1
- 左手邊是 Agda code
- Vector Space (without Scalars)的例子 (group: closed associate, identity), 詳細介紹例子
- Translation 基於 Agda reflection
- Agda reflection 是一種內建於 Agda 的 metaprogramming system
- 而右手邊是 smtlib format，可以被 Vampire 當作輸入格式
- 我會先介紹一下 Agda 會用到 equality definition 和 Agda 的證明方式，給不熟悉 Agda 的人，可以理解如何操作 Proof Object 的方式來證明。
## A Little Taste of Agda
- 簡單介紹一下 Agda 的證明方式：
- 上面三個是 equality relation (Agda lib)
- 下面兩個是我們的前面例子定義的
## Contents
我前面介紹完了動機與背景知識，接下來會來介紹
- Classical FOL
- Vampire Core Calculus
- Vampire to Agda 的流程 (也會是我的 Thesis Proposal 主要關注的重點)
- Thesis Proposal
## Classical FOL
- term
- atom: 特別把 equality 這個 predicate 拿出來，是因為很大一部分的證明是找出兩個 formula 的等價關係。就像是我會使用 equality reasoning 的方式去證明。
- literal: 為什麼要特別提出 literal 這個 terminology 來描述 atom 呢？ 因為 ATP 使用 classical proof 的方式去證明程式。且自動化證明也會經過預處理的方式，轉成 Conjunction Normal Form (Clause Normal Form)，而在轉乘 CNF 前會先轉換成 Negation Normal Form，NNF 就是把所有的 negation 移到 atom 旁邊。
- formula
- Key point
- Refutation Proof
## Horn Clause and Notation
- FOL clause
- Horn clause
    1. definite clause
    2. goal clause
- (補充)Constructive Valid ???
## Vampire Core Calculus (VCC)
- Resolution:
- Factoring:
- Superpostion:
- Equal Resolution:
- mgu ...
- "[ ]" 's meaning 
- footnote
## Example 1
下面是 Vampire 找到的證明，而上面是整理下面的證明後的易讀版本
- neutl
- negl
- assoc
- negate conjecture
- 用到 superpostion 和最後使用到 resolution
接下來我會詳細介紹這證明中的step 6的展開形式
## Example 1's Step 6
step 6 : 對 negl 和 assoc 使用 superposition 來得到 step 6 的 theorem。
- negl: left hand side of sup
- assoc: right hand side of sup
- unification: ???
## A classical proof to intuitionistic proof
接下來會介紹最重要的部分是 從 Vampire 到 Agda, 從 Classical 到 Intuitionistic
我們會限制這兩邊的系統在 Horn Clause 的情況下。
...
## Lemmas
- Lemma 1:
- Lemma 2: Constructive Valid?
- Lemma 3: ???
## VCC and HVCC (Lemma 1)
左手邊是原本的 VCC，而右手邊是 Horn 版的 VCC
我可以用 RES 和 SUP 來舉例 Horn 版本的 VCC
- RES
- SUP: 這邊 Superpostion 分成 left 和 right 的主要原因是因為要把 A[l'] 是作為 Positive 或是 negation 的，所以就分出了兩個 inference rule
## HVCC and HVCC$^Imp
## HVCC and Agda (Propositions as types) (Lemma 2)
## Example 2 (Lemma 3)
## Thesis Proposal