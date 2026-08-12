Your job is to formalize the 3 admitted results in Kedlaya.lean. The main reference is the following paper of Kedlaya:
1. [Kedlaya2001a] K. Kedlaya, "The algebraic closure of the power series field in positive characteristic", Proc. Amer. Math. Soc. 129 (2001), no. 12, 3461–3470.
2. [Kedlaya2001b] K. Kedlaya, "Power Series and p-Adic Algebraic Closures", J. Number Theory 89 (2001), no. 2, 324–339.
3. [Kedlaya2017] K. Kedlaya, "On the algebraicity of generalized power series", Beitr Algebra Geom 58 (2017), no. 3, 499-527.


# General notes
1. I have downloaded these paper for you and put them in the /refs folder. Besides, I provides the LaTeX source of these papers in the same folder, which may be better for you to read. **Note**: The published pdf and arxiv .tex files are not exactly the same, please be very careful, And when I refer to a theorem, lemma, or definition in Kedlaya's papers, I will always give you the page number of the published pdf.
2. As is recored in [Kedlaya2017, Section 2], the main result of [Kedlaya2001a] is **FALSE** in general, and it affects [Kedlaya2001b]. However, as is also noted in the same paper, the main result of [Kedlaya2001a] is still **TRUE** if we only consider the case of `K=F_p^bar`, i.e. the algebraic closure of the finite field of characteristic p. In this project, we only consider this case, so Kedlaya's results are still **VALID** for us.
3. There are numerous typos in Kedlaya's papers, which affect the reading of the papers. For example, the set `S_{a,b,c}` appears in different places in Kedlaya's papers, but the definition is not consistent. I have fixed this single definition in the file `Kedlaya.lean`, which should be the correct one. There maybe many other typos in Kedlaya's papers, so please be extremely careful when reading the papers.
4. The purpose of this project is **NOT** to give a fully formalization of Kedlaya's 3 papers, but only to formalize the 3 admitted results. So you should try to formalize as less code as possible. In particular,
    (a) if a result in his papers is not used in the proof of the 3 admitted results, you should **NOT** formalize it.
    (b) Some result states in an `if and only if` form, but we only need one direction of it, you should **NOT** formalize the other direction.
    (3) Kedlaya states his results for general (algebraically closed) fields `K` of characteristic `p`, but we only need the case of `K=F_p^bar`, so you must be specialized to this case.
5. The size of this project is expected to be very large, so you should try to formalize the results in a **modular** way. Multiple files are allowed and recommended.
6. Please keep the code well-documented.

# Notes on the 3 admitted results
1. `kedlaya_2001a_theorem15_half`
    (1a) This is "a half" of [Kedlaya2001a, Theorem 15] (or [Kedlaya2017, Theorem 11.11]). You don't need to prove the other direction.
    (1b) The proof of [Kedlaya2001a, Theorem 8] is false for general `K`, as noted in [Kedlaya2017, Section 2]. This affects [Kedlaya2001a, Theorem 15], but as is noted in [Kedlaya2017, Section 2], the whole theory in [Kedlaya2001a] still holds for `K=F_p^bar`.
    (1c) The proof of this theorem in [Kedlaya2001a] and [Kedlaya2017] is different. In [Kedlaya2001a], he uses twist-recurrent sequences + Artin-Schreier theory, while in [Kedlaya2017], he uses autometa theory. Both paper need outputs from the outside. Please think carefully which one is easier and faster to formalize. You should pick the easier one to formalize. Do **NOT** do the both, which will waste much time and money for token.

2. `kedlaya_2017_theorem13_4`
    (2a) This is just a part of [Kedlaya2017, Theorem 13.4]. Don't try to formalize the whole theorem.
    (2b) I think theo core of `kedlaya_2017_theorem13_4` lies in [Kedlaya2001b,Theorem 13.4].
    (3c) This theorem massively use the theory of Witt vectors. You may have to develop some results on Witt vectors in Lean.
    (3d) Remember, only focus on the case of `K=F_p^bar`, and don't try to formalize the general case. There are many unrelated results in Kedlaya's papers, which are not needed for our purpose. You should **NOT** formalize them.
    (3d) I'm not sure when you formalize this result, you may need to formalize the fact that the field `𝕃_[p]` of p-adic Hahn series with residue field `F_p^bar` and value group `ℚ` is algebraically closed. This is proved in [Kedlaya2001b, Section 1], but the proof is not well written. You can also refer to Section 2 of WangYuan.pdf in /refs, which reprase Kedlaya's approach in a clearer manner.

3. `kedlaya_2001b_ordinal_bound`
    (3a) This appears at the end of [Kedlaya2001b, Section 4]. Kedlaya claimed that this is a corollary of [Kedlaya2001b, Theorem 11] without proof. You many need to figure out the proof by yourself.