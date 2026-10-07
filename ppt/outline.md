# Transcript
> ... : follow up ppt's content

## Title
"When Agda met Vampire" 是一篇2026年的 preprint 的 paper。
這篇論文主要貢獻是提供 Agda 和 Vampire 之間的轉換。
而我的 Thesis Proposal 是從這篇轉換去做延伸。
## Background
- ATP
- ITP
- Vampire 的歷史與獎項:
    - CASC 是全稱是 CADE ATP System Competition, 是由 CADE 和 IJCAR 所舉辦的 ATP 競賽
    - CADE: Conference on Automated Deduction
    - IJCAR: Internation Joint Conference on Automated Reasoning
- ATP 和 ITP 的結合, tactics and Hammer
- 接下來看論文主要的架構
## Motivation
- 雙方可以得到的好處:
    - Agda: 有好的自動證明
    - Vampire: 能更確認他的輸出的證明是正確的
- 所以這張圖片給了我們這篇論文的核心運作原理：
1. 首先看下面的這個箭頭，我們會從一段 agda 程式開始，把 Agda 的程式翻譯成 Vampire。
2. 轉換完成後，讓 Vampire 基於這些 Axioms, Theorems 和 conjecture，來自動找出證明。
3. 再來就是把 Vampire 最終的輸出 (證明過程)，轉換成 Agda 的程式，這也會是我的 Thesis Proposal 主要要做的部分
4. 最後產生出來的 Agda program 在經由 agda typechecking 來做驗證來確保 Vampire 最終輸出證明的正確性。
- Tactics:
    Lean4 有強大的 grind tactic, Coq 有強大的 CoqHammer, Isebelle 有強大的 Sledgehammer, 但 Agda 缺乏強大的 auto tactic。
- 可以來看看一個麻煩的例子。
## Example 1
- 左手邊是 Agda code
- Vector Space (without Scalars)的例子 其實是一個 group (group: closed associate, identity), 詳細介紹例子
- Translation 基於 Agda reflection
- Agda reflection 是一種內建於 Agda 的 metaprogramming system
- 而右手邊是 smtlib format，可以被 Vampire 當作輸入格式
- 我會先介紹一下 Agda 會用到 equality definition 和 Agda 的證明方式，給不熟悉 Agda 的人，可以理解如何操作 Proof Object 的方式來證明。
## A Little Taste of Agda
- 簡單介紹一下 Agda 的證明方式：
會用到 5 個 definition，上面三個是 equality relation (Agda lib),下面三個是我們的前面例子定義的:
- sym: 如果 x equal to y， 基於 symmetric rule 我可以得到 y equal to x
- cong: 如果 x equal to y, 基於 congruence rule 我可以得到 fx equal to fy
- trans: 如果 x equal to y 和 y equal to z, 基於 transtive rule 我可以得到 x equal to z.
- neutl: zero vector 加上 vector 等於 這個 vecotr
- negl: negative vector 加上 positive vector 會等於 zero vector
- assoc: 就是我們知道的結合律

trivial 就是我們想要證明的目標，一個 negative vector 加上 兩個 positive vectors 等於 一個 positve vector。
- t1: 從上面的 type 上我們可以看到，我們對左手邊的公式的括號，由右往左移動，使用到 assoc -u u u，在對它做 sym 就得到了這個公式
- t2: 一樣看到左手邊的這個括號等於 zero vector，所以我們會對右手邊的這個 + u，做 cong (negl)
- ans: 在基於 transive rule 來把 t1 和 t2 接起來，在 trans 前面這一塊和 neutl u
## Contents
我前面介紹完了動機與背景知識，前面介紹的內容就是動機裡面下面的箭頭，從Agda 到 Vampire 的過程。而我們接下來會看到剩下的三個步驟，是如何進行的。
- Classical FOL: 因為前面提到 ATP 都是基於 Classical FOL，來做自動證明，所以我會介紹到 ATP 所需要的內容。
- Vampire Core Calculus: 再來會介紹到 Vampire Core Calculus，來理解 Vampire 內部是如何自動找出證明的
- Vampire to Agda 的流程就是對應到前面那張圖片上面的箭頭，也會是我的 Thesis Proposal 主要關注的重點，如何從 Classical 到 Intuitionistic
- Thesis Proposal
## Classical FOL
- term
- atom: 特別把 equality 這個 predicate 拿出來，是因為很大一部分的證明是找出兩個 term 的等價關係。就像是我會使用 equality reasoning 的方式去證明。
- literal: 為什麼要特別提出 literal 這個 terminology 來描述 atom 呢？ 因為 ATP 使用 classical proof 的方式去證明程式。且自動化證明也會經過預處理的方式，轉成 Conjunction Normal Form (Clause Normal Form)，而在轉乘 CNF 前會先轉換成 Negation Normal Form，NNF 就是把所有的 negation 移到 atom 旁邊。
- formula
- Key point
- Refutation Proof
## Horn Clause and Notation
- FOL clause
- Horn clause: 基於 FOL clause 再加上新的限制
    1. definite clause: 基於 logic programming 的方式來證明(head :- body)，直觀的理解，就是由一堆前提推出一個結論
    2. goal clause: 因為 refutation proof 的關係，所以需要把 goal 做 negation，就會的得到下面這個形式。
## Vampire Core Calculus (VCC)
這邊還是一般 Clause form。 (避免被誤解成 Horn VCC)
John Robinson 發明出一個 Resolution (Resolution rule and Factoring rule)，希望有一個像是 Hilbert System (many axioms 和 one inference rule)的自動化證明系統。 
- 所有要經過 Core Calculus 的 input，都會被先預處理成 CNF。
- Resolution(eliminate clause): input 2 clause, output 1 clause，來達到消減 clause 的數量。
- Factoring(eliminate literal): input 1 clause, output 1 個
- Superpostion: Resolution + Equality(Reflexivity rule + Replacement rule) = Paramodulation. And Superposition is a strict order Paramodulation.
- Equal Resolution: Just like Factoring, working with Superposition.
所以就可以看到左手邊的 rules 著重在消減 clause 的數量，而右手邊的 rules 著重在消減重複 literal 的數量。
這邊的 rules 並沒有維持 equivalent，但是他是基於 equisatisfiability. (Inference rule 的 premises 是 SAT, conclusion 也會是 SAT. 同樣的，premises 是 UnSAT，conclusion 夜會是 UnSAT)
- mgu
- "A[l']": 是帶有 l' 的 atomic
- footnote
## Example 1
下面是 Vampire 找到的證明，而上面是整理下面的證明後的易讀版本
- neutl
- negl
- assoc
- negate conjecture
- 用到 大量的 superpostion 和最後使用到 resolution
接下來我會詳細介紹這證明中的step 6的展開形式
## Example 1's Step 6
step 6 : 對 negl 和 assoc 使用 superposition 來得到 step 6 的 theorem。
- negl: left hand side of sup，negative vector 加上 positive vector = zero vector
- assoc: right hand side of sup
- unification: 對著 l 和 l' 做 unify，讓 l' 可以 rewrite 成 r 
## A classical proof to intuitionistic proof
- 接下來會介紹最重要的部分是 從 Vampire 到 Agda, 從 Classical 到 Intuitionistic
- 我們證明的形式會是 Gamma entail G。
1. 我們會限制 Vampire 在 Horn Clause 的情況下。基於 Vampire 的 proof by refutation，變成 Gamma and neg G entail bot. 在轉換成 implication 的形式。
2. 完整的 vampire core calculus 是 classical proof，但是經過限制成 horn 版本，就可以 intuitionistic valid. (為什麼是 intuitionistic valid? 來源可以看 Dale Miller's Uniform proofs Thm1, first-order horn clause(fohc) is even minimal valid. )
3. 經過轉換過後，最後可以把 bot 都替換成 G，就可以很直接的得到 Gamma entail G 在 intuitionistic proof.
## Lemmas
- Lemma 1: 所有的 VCC rules, 如果 premises 是 horn, 則 conclusion 也會是 horn. 且我們會基於把 disj 的形式，轉換成 conj 和 imply 的形式
- Lemma 2: Horn Vampire Core Calculus 是 intuitionistically valid. 這會是我的 Thesis 需要去證明的方向。
- Lemma 3: 當 Gamma 是 definite clauses 和 G 是 ground atom。 如果 ... 被 HVCC 推導出來，則 ... 也會被 HVCC 推導出來。
## Proof of Lemma 1
左手邊是原本的 VCC，而右手邊是 Horn 版的 VCC
我可以用 RES 和 SUP 來舉例 Horn 版本的 VCC, 因為 Horn 版本的所以我們會特別用 boxed 來表示 positive atom.
- RES: 這邊 input 兩個 Horn clause，所以 左手邊的這個 horn clause: A 就會是 positive，而Ｃ就會像是 goal clause 那樣全是 negative 的 literal。 那右手邊的 D 就會像是 definite clause 那樣存在一個 positive atom B。
- SUP: 這邊 Superpostion 分成 left 和 right 的主要原因是因為要把 A[l'] 是作為 Positive 或是 negation 的，所以就分出了兩個 inference rule。 那為什麼 SUP.R 不需要 boxed 呢？ 因為這個 rule 沒有 bot 需要被替換，所以不用特別把它 boxed。 然後介紹 SUP.L SUP.R 為什麼是 horn。
- 其他 rules 也可以基於這樣的形式去轉換成 horn 版本
## HVCC
基於前面的 horn clause 的 clause 形式轉換成 Implication, 就可以得到 Horn Vampire Core Calculus (HVCC)
## Proof of Lemma 2
這邊我們把 proposition 都轉換成 Agda 上的 type，基於 Propositions as Types and Proof as Program!!，那也可以把證明轉換成 Agda 上面的程式。
這邊我就用 Factoring 和 Superpostion left rule，來解釋一下怎麼做轉換的。
- FAC: 這邊 mgu(A, A')，可以來看 exmple 1 (step6)，因為 vampire 輸出的證明已經是經過 unification 之後的證明，所以我們就不用特別區分 A 或是 A'，可以把他們當作同一個 type 來看。
- SUP.L: 同樣的經過 mgu(l, l')，也可以把 l 跟 l' 是作為同一個 type。 先對 sym (t_1 p) 得到type r = l， subst (sym (t_1 p)) a 這邊的 a 是type A[r] 得到type A[l]，...
- 其他 rules 也可以基於 "Propositions as types" 和 "Proof as Program" 的方式來達成轉換。
## An example of applying Lemma 3
- Gamma: t1, t2, t3
- G: t4: a = b
這邊我們可以先有一個直觀理解的證明，a = f(c) 且 b = c，我就可以有 a = f(b)，之後又基於 a = b 和 t1，我們可以知道這個證明會是對的。
...
當然這邊的證明會有很多種形式，但是最終都能推導出一樣的結論。
## Thesis Proposal
...