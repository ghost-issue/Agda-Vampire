# Transcript
## Title
"When Agda met Vampire" 是一篇2026年的 preprint 的 paper，是由 Vampire 團隊成員所撰寫的。
這篇論文主要貢獻是提供 Agda 和 Vampire 之間的轉換。
而我的 Thesis Proposal 是從這篇去做延伸。
## Background
- ATP
- ITP
- Vampire 的歷史與獎項
- ATP 和 ITP 的結合
- 接下來看論文主要的架構
## Motivation
- Tactics:
    Lean4 有強大的 grind tactic, Coq 有強大的 CoqHammer, Isebelle 有強大的 Sledgehammer, 但Agda 缺乏強大的 auto tactic。
- 可以來看看一個麻煩的例子。
## Example 1
- 左手邊是 Agda code
- Vector Space (without Scalars)的例子 (group: closed associate, identity), 詳細介紹例子
- Translation 基於 Agda reflection
- Agda reflection 是一種內建於 Agda 的 metaprogramming system
- 而右手邊是 smtlib format，可以被 Vampire 當作輸入格式
## A Little Taste of Agda
- 簡單介紹一下 Agda 的證明方式：
- 上面三個是 equality relation (Agda lib)
- 下面兩個是我們的前面例子定義的
## Contents
## Classical FOL
## Horn Clause and Notation
## Vampire Core Calculus (VCC)
## Example 1
## Example 1's Step 6
## A classical proof to intuitionistic proof
## Lemmas
## VCC and HVCC
## HVCC and HVCC$^Imp
## HVCC and Agda (Propositions as types)
## Example 2
## Thesis Proposal