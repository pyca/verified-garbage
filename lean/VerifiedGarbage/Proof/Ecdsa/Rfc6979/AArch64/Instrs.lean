module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Hash
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff

/-!
# Deterministic ECDSA on AArch64: no instruction writes a callee-saved SIMD register

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Instrs.lean`). For code `c`
(`Impl.Ecdsa.Rfc6979.AArch64.Cfg`) whose blocks of the curve's and the hash
function's sizes write none (`RfcT`, which each curve's file checks; the
blocks that differ from those only in offsets and immediates by
`Instr.eraseOff`), whose table's functions write none (`FnsKeep`) and whose
`core` writes none: the whole function (`sign_keepP`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- No instruction of `x` writes a callee-saved SIMD register. -/
abbrev KeepP (x : Prog isa) : Prop := x.allInstrs keepsV = true

theorem keepP_seq {a b : Prog isa} (ha : KeepP a) (hb : KeepP b) : KeepP (.seq a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem keepP_ite {cnd : Cond} {a b : Prog isa} (ha : KeepP a) (hb : KeepP b) : KeepP (.ite cnd a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem keepP_loop {cnd : Cond} {a : Prog isa} (ha : KeepP a) : KeepP (.loop a cnd) := ha

theorem keepP_call {n : String} {a : Prog isa} (ha : KeepP a) : KeepP (.call n a) := ha

theorem okB_append {a b : List Instr} (ha : OkB a) (hb : OkB b) : OkB (a ++ b) := by
  unfold OkB at *
  rw [Code.allInstrs_eq] at ha hb ⊢
  simp only [instrs, List.all_append, Bool.and_eq_true] at ha hb ⊢
  exact ⟨ha, hb⟩

/-- A block that differs from a checked one only in offsets and immediates. -/
theorem okB_erase {is is₀ : List Instr} (h : OkB is₀) (he : is.map Instr.eraseOff = is₀.map Instr.eraseOff) :
    OkB is :=
  Code.allInstrs_keepsV_of_eraseOff_eq (c' := .block is₀) (congrArg Code.block he) h

theorem icalls_keepP {ts : List (String × Prog isa)} (h : FnsKeep ts) : KeepP (Code.icalls (.blr .x16) ts) := by
  induction ts with
  | nil => rfl
  | cons q ts ih =>
    obtain ⟨n, b⟩ := q
    show (keepsV (.blr .x16) && b.allInstrs keepsV && (Code.icalls (.blr .x16) ts).allInstrs keepsV) = true
    rw [h _ (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

theorem tcall_keepP {j : Nat} {ts : List (String × Prog isa)} (h : FnsKeep ts) : KeepP (Cfg.tcall j ts) :=
  keepP_seq rfl (keepP_seq rfl (icalls_keepP h))

variable {c : Cfg} (hT : RfcT c) (hf : FnsKeep c.f.init ∧ FnsKeep c.f.upd ∧ FnsKeep c.f.fin)
include hf

theorem initCall_keepP (o : Nat) : KeepP (c.initCall o) := keepP_seq rfl (tcall_keepP hf.1)

theorem updCall_keepP (o cnt : Nat) {dataA : List Instr}
    (hd : (∃ a, dataA = Cfg.scr .x2 a) ∨ (∃ a, dataA = Cfg.fr .x2 a)) (len : Nat) :
    KeepP (c.updCall o cnt dataA len) := by
  refine keepP_seq ?_ (tcall_keepP hf.2.1)
  rcases hd with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rfl
  · rfl

theorem finCall_keepP (o cnt : Nat) : KeepP (c.finCall o cnt) := keepP_seq rfl (tcall_keepP hf.2.2)

include hT

omit hf in
theorem padBlk_keepP (x : BitVec 32) : KeepP (.block (c.padBlk x)) :=
  okB_append rfl (okB_erase hT.iPad (by simp only [Cfg.padBody, List.map_append]; rfl))

theorem hinit_keepP : KeepP c.hinit :=
  keepP_seq (initCall_keepP hf _) (keepP_seq (initCall_keepP hf _) (keepP_seq (padBlk_keepP hT _) (keepP_seq
    (updCall_keepP hf _ _ (.inl ⟨_, rfl⟩) _) (keepP_seq (padBlk_keepP hT _)
      (updCall_keepP hf _ _ (.inl ⟨_, rfl⟩) _)))))

theorem hfin_keepP (len dst : Nat) : KeepP (c.hfin len dst) :=
  keepP_seq (finCall_keepP hf _ _) (keepP_seq (updCall_keepP hf _ _ (.inl ⟨_, rfl⟩) _)
    (keepP_seq (finCall_keepP hf _ _)
      (okB_append rfl (okB_erase hT.iCopy (by simp only [Cfg.copyOut, List.map_append]; rfl)))))

theorem hmac_keepP {dataA : List Instr} (hd : (∃ a, dataA = Cfg.scr .x2 a) ∨ (∃ a, dataA = Cfg.fr .x2 a))
    (len dst : Nat) : KeepP (c.hmac dataA len dst) :=
  keepP_seq (hinit_keepP hT hf) (keepP_seq (updCall_keepP hf _ _ hd _) (hfin_keepP hT hf _ _))

theorem hmacV_keepP : KeepP c.hmacV := hmac_keepP hT hf (.inr ⟨_, rfl⟩) _ _

theorem rekeyFull_keepP (b : Nat) : KeepP (c.rekeyFull b) :=
  keepP_seq rfl (keepP_seq (okB_erase hT.iMsgF (by simp only [Cfg.msg, List.map_append]; rfl))
    (keepP_seq (hmac_keepP hT hf (.inl ⟨_, rfl⟩) _ _) (hmacV_keepP hT hf)))

theorem rekey_keepP : KeepP c.rekey :=
  keepP_seq rfl (keepP_seq hT.iMsgN (keepP_seq (hmac_keepP hT hf (.inl ⟨_, rfl⟩) _ _) (hmacV_keepP hT hf)))

theorem candW_keepP : ∀ k, KeepP (c.candW k)
  | 0 => rfl
  | k + 1 => keepP_seq (candW_keepP k) (keepP_seq (hmacV_keepP hT hf)
      (okB_erase hT.iKeepV (by simp only [Cfg.keepV, List.map_append]; rfl)))

theorem cand_keepP : KeepP c.cand := by
  unfold Cfg.cand
  split
  · refine keepP_seq (candW_keepP hT hf _) ?_
    unfold Cfg.candTop
    split
    · rfl
    · exact keepP_seq rfl hT.iCandTop
  · exact hmacV_keepP hT hf

theorem tryOne_keepP (hcore : KeepP c.coreC) : KeepP c.tryOne :=
  keepP_seq (cand_keepP hT hf) (keepP_seq hT.iCoreArgs (keepP_call hcore |> fun h => keepP_seq h (keepP_seq rfl
    (keepP_ite (keepP_seq (rekey_keepP hT hf) rfl) rfl))))

/-- The frame's body and the function: no instruction writes a callee-saved SIMD register. -/
theorem sign_keepP (hcore : KeepP c.coreC) : KeepP c.sign := by
  have hb : KeepP c.body :=
    keepP_seq rfl (keepP_seq hT.iDigestPtr (keepP_seq hT.iPrep (keepP_seq (rekeyFull_keepP hT hf 0)
      (keepP_seq (rekeyFull_keepP hT hf 1) (keepP_seq rfl (keepP_seq (keepP_loop (tryOne_keepP hT hf hcore))
        hT.iWipe))))))
  show (keepsV _ && (keepsV _ && c.body.allInstrs keepsV && keepsV _) && keepsV _) = true
  rw [hb]; rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
