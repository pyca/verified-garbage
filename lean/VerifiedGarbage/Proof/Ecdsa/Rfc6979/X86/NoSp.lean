module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Hash
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Deterministic ECDSA on x86 (32-bit): no instruction writes `esp`

`NoSp` of the frame's body (`body_nosp`), from `NoSp` of its pieces: the
blocks, by evaluating which registers they write (`NoSp.block`), whatever the
sizes of the hash function and the curve, and the calls, by what `P` knows
of the functions of every hash function the code may call (`fnsSp`) and of
`core`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

theorem NoSp.seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [instrs, List.mem_append] at hi; rcases hi with h | h; exacts [ha i h, hb i h]

theorem NoSp.ite {c : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite c a b) := fun i hi => by
  simp only [instrs, List.mem_append] at hi; rcases hi with h | h; exacts [ha i h, hb i h]

theorem NoSp.loop {c : Cond} {a : Prog isa} (ha : NoSp a) : NoSp (.loop a c) := fun i hi => ha i hi

theorem NoSp.call {n : String} {a : Prog isa} (ha : NoSp a) : NoSp (.call n a) := fun i hi => ha i hi

theorem NoSp.frame {x y : Instr} {a : Prog isa} (hx : Taint.clobbers x .esp = false) (hy : Taint.clobbers y .esp = false)
    (ha : NoSp a) : NoSp (.frame x a y) := fun i hi => by
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | h) | rfl
  exacts [hx, ha i h, hy]

theorem NoSp.block {is : List Instr} (h : is.all (fun i => !Taint.clobbers i .esp) = true) : NoSp (.block is) :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem NoSp.chain {r : Reg} (hr : r ≠ .esp) : ∀ {cs : List (Nat × Prog isa)}, (∀ c ∈ cs, NoSp c.2) →
    NoSp (Impl.Dispatch.X86.chain r cs)
  | [], _ => NoSp.block rfl
  | [(_, c)], h => h _ List.mem_cons_self
  | (k, c) :: c' :: cs, h => NoSp.seq (NoSp.block (by
      simp [Impl.Dispatch.X86.test, Taint.clobbers, Taint.dst, hr]))
    (NoSp.ite (h _ List.mem_cons_self) (NoSp.chain hr fun c hc => h c (List.mem_cons_of_mem _ hc)))

theorem all_nosp_append {a b : List Instr} (ha : a.all (fun i => !Taint.clobbers i .esp) = true)
    (hb : b.all (fun i => !Taint.clobbers i .esp) = true) : (a ++ b).all (fun i => !Taint.clobbers i .esp) = true := by
  rw [List.all_append, ha, hb]; rfl

theorem copyN_nosp (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) :
    (copyN k src so dst d).all (fun i => !Taint.clobbers i .esp) = true := by
  simp [copyN, List.all_flatMap, Taint.clobbers, Taint.dst]

theorem zeroN_nosp (k o : Nat) : (zeroN k o).all (fun i => !Taint.clobbers i .esp) = true := by
  simp [zeroN, Taint.clobbers, Taint.dst]

theorem copyBytes_nosp (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d : Nat) :
    (copyBytes k src so dst d).all (fun i => !Taint.clobbers i .esp) = true := by
  refine all_nosp_append (copyN_nosp _ _ _ _ _) ?_
  split <;> simp [Taint.clobbers, Taint.dst]

variable (P : RfcHash)

theorem calls_nosp {mk : Impl.Pbkdf2.Whole.X86.Fns → Prog isa} (h : ∀ p ∈ P.fns, NoSp (mk p.2)) :
    NoSp ((cfgOf P).calls mk) :=
  NoSp.chain (by decide) fun c hc => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
    exact h p hp

theorem hmac_nosp (dataA : List Instr) (hd : dataA.all (fun i => !Taint.clobbers i .esp) = true) (lenS totS dst : Nat) :
    NoSp ((cfgOf P).hmac dataA lenS totS dst) := by
  have blk : ∀ is : List Instr, is.all (fun i => !Taint.clobbers i .esp) = true → NoSp (.block is) := fun _ h =>
    NoSp.block h
  refine NoSp.seq (blk _ (by simp [hmacArgs₁, scr, fr, selArg, argM, Taint.clobbers, Taint.dst]))
    (NoSp.seq (NoSp.frame rfl rfl (calls_nosp P fun p hp => NoSp.call (P.fnsSp p hp).1))
    (NoSp.seq (blk _ ?_) (NoSp.seq (NoSp.frame rfl rfl (calls_nosp P fun p hp => NoSp.call (P.fnsSp p hp).2.1))
    (NoSp.seq (blk _ (by simp [hmacArgs₃, scr, fr, selArg, argM, Taint.clobbers, Taint.dst]))
      (NoSp.frame rfl rfl (calls_nosp P fun p hp => NoSp.call (P.fnsSp p hp).2.2))))))
  simp only [hmacArgs₂, List.all_append, hd]
  simp [scr, selArg, argM, Taint.clobbers, Taint.dst]

theorem hmacV_nosp : NoSp (cfgOf P).hmacV := hmac_nosp P _ (by simp [fr, Taint.clobbers, Taint.dst]) _ _ _

theorem rekeys_nosp (b : Nat) (full : Bool) (lenS totS : Nat) :
    NoSp (.seq (.block msgPtrs) (.seq (.block msgV) (.seq (.block (msgTail P.Q b full))
      (.seq ((cfgOf P).hmac (scr .edx sMsg) lenS totS fK) (cfgOf P).hmacV)))) := by
  refine NoSp.seq (NoSp.block (by simp [msgPtrs, argM, Taint.clobbers, Taint.dst]))
    (NoSp.seq (NoSp.block (all_nosp_append (copyN_nosp _ _ _ _ _) (by simp [Taint.clobbers, Taint.dst])))
    (NoSp.seq (NoSp.block ?_) (NoSp.seq (hmac_nosp P _ (by simp [scr, argM, Taint.clobbers, Taint.dst]) _ _ _)
      (hmacV_nosp P))))
  refine all_nosp_append (by simp [Taint.clobbers, Taint.dst]) ?_
  split
  · exact all_nosp_append (copyBytes_nosp _ _ _ _ _) (copyBytes_nosp _ _ _ _ _)
  · rfl

theorem subWord_nosp (c : Cfg) (j : Nat) : (c.subWord j).all (fun i => !Taint.clobbers i .esp) = true := by
  cases j <;> rfl

theorem selWord_nosp (c : Cfg) (j : Nat) : (c.selWord j).all (fun i => !Taint.clobbers i .esp) = true := rfl

/-- `h = X mod n`, `K` and `V`, whatever the code's `n`. -/
theorem reduceKV_nosp (c : Cfg) : (c.reduce ++ initKV).all (fun i => !Taint.clobbers i .esp) = true := by
  simp only [Cfg.reduce, List.all_append, List.all_flatMap, subWord_nosp, selWord_nosp]
  rw [show ∀ l : List Nat, (l.all fun _ => true) = true from fun l => List.all_eq_true.mpr fun _ _ => rfl]
  decide

theorem setup_nosp : NoSp (cfgOf P).setup :=
  calls_nosp P fun p _ => NoSp.block (all_nosp_append (by simp [Cfg.storeSizes, Cfg.sizes, Taint.clobbers, Taint.dst])
    (by
      simp only [Cfg.digestX]
      split
      · exact copyN_nosp _ _ _ _ _
      · split
        · exact all_nosp_append (zeroN_nosp _ _) (copyN_nosp _ _ _ _ _)
        · exact all_nosp_append (all_nosp_append (all_nosp_append (zeroN_nosp _ _) (copyN_nosp _ _ _ _ _))
            (zeroN_nosp _ _)) (copyN_nosp _ _ _ _ _)))

/-- The conversions of P-521's sizes. -/
theorem conv_nosp (hW : P.R.wide = true) {o s : Nat} (h : (o = fX ∧ s = 8 - (cfgOf P).sh) ∨ (o = fC ∧ s = (cfgOf P).sh)) :
    ((cfgOf P).conv o s).all (fun i => !Taint.clobbers i .esp) = true := by
  have hQ : (cfgOf P).len = 66 := (P.sizesW hW).2.1
  have h7 : (cfgOf P).sh = 7 := (P.sizesW hW).2.2
  rw [h7] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [Cfg.conv, hQ] <;> decide +kernel

theorem prep_nosp : NoSp (cfgOf P).prep := by
  simp only [Cfg.prep]
  split
  · exact NoSp.block (reduceKV_nosp _)
  · rename_i h
    have hW : P.R.wide = true := by
      cases hW : P.R.wide
      · exact absurd (P.sh0 hW) h
      · rfl
    exact NoSp.seq (NoSp.block (by simp [scrPtr, argM, Taint.clobbers, Taint.dst]))
      (NoSp.block (all_nosp_append (conv_nosp P hW (.inl ⟨rfl, rfl⟩)) (by decide)))

theorem cand_nosp : NoSp (cfgOf P).cand := by
  refine NoSp.seq (NoSp.block (by simp [candInit, Taint.clobbers, Taint.dst]))
    (NoSp.seq (NoSp.loop (NoSp.seq (hmacV_nosp P) (NoSp.seq (NoSp.block (by simp [candAt, fr, Taint.clobbers, Taint.dst]))
      (NoSp.block (all_nosp_append (copyN_nosp _ _ _ _ _) (by simp [Taint.clobbers, Taint.dst])))))) ?_)
  split
  · exact NoSp.block rfl
  · rename_i h
    have hW : P.R.wide = true := by
      cases hW : P.R.wide
      · exact absurd (P.sh0 hW) h
      · rfl
    exact NoSp.seq (NoSp.block (by simp [scrPtr, argM, Taint.clobbers, Taint.dst])) (NoSp.block (conv_nosp P hW (.inr ⟨rfl, rfl⟩)))

theorem tryOne_nosp : NoSp (cfgOf P).tryOne :=
  NoSp.seq (cand_nosp P) (NoSp.seq (NoSp.block (by simp [coreArgs, fr, argM, Taint.clobbers, Taint.dst]))
    (NoSp.seq (NoSp.frame rfl rfl (NoSp.call P.R.coreNs)) (NoSp.seq (NoSp.block (by decide))
      (NoSp.ite (NoSp.seq (rekeys_nosp P _ _ _ _) (NoSp.block (by decide))) (NoSp.block (by decide))))))

/-- No instruction of the body writes `esp`: not those of the functions it
calls, by what `P` knows of them, nor its own. -/
theorem body_nosp : NoSp (cfgOf P).body :=
  NoSp.seq (NoSp.block (by decide)) (NoSp.seq (setup_nosp P) (NoSp.seq (prep_nosp P)
    (NoSp.seq (rekeys_nosp P _ _ _ _) (NoSp.seq (rekeys_nosp P _ _ _ _)
    (NoSp.seq (NoSp.block (by simp [Cfg.initCnt, Taint.clobbers, Taint.dst]))
    (NoSp.seq (NoSp.loop (tryOne_nosp P)) (NoSp.block (by decide))))))))

end VG.Proof.Ecdsa.Rfc6979.X86
