module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve

/-!
# Deterministic ECDSA on AArch64: no instruction writes a callee-saved SIMD register

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Instrs.lean`), for `keepsV`: for
code `c` (`Impl.Ecdsa.Rfc6979.AArch64.Cfg`) whose blocks of the curve keep
the callee-saved SIMD registers (`RfcT`, which each curve's file checks),
whose table's functions keep them (`FnsOk`) and whose `core` keeps them:
the frame's body (`body_okP`), and so the whole function (`sign_okP`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- No instruction of `x` writes a callee-saved SIMD register. -/
abbrev OkP (x : Prog isa) : Prop := x.allInstrs keepsV = true

theorem okP_seq {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.seq a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem okP_ite {cnd : Cond} {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.ite cnd a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem okP_loop {cnd : Cond} {a : Prog isa} (ha : OkP a) : OkP (.loop a cnd) := ha

theorem okP_call {n : String} {a : Prog isa} (ha : OkP a) : OkP (.call n a) := ha

/-- Nor in any of the functions `ts`. -/
def FnsOk (ts : List (String × Prog isa)) : Prop := ∀ q ∈ ts, OkP q.2

theorem icalls_okP : ∀ {ts : List (String × Prog isa)}, FnsOk ts → OkP (Code.icalls (.blr .x16) ts)
  | [], _ => rfl
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_okP (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    show (Code.icalls (.blr .x16) (q :: ts)).allInstrs keepsV = true
    simp only [Code.icalls, Code.allInstrs, show q.2.allInstrs keepsV = true from hq,
      show (Code.icalls (.blr .x16) ts).allInstrs keepsV = true from ih, Bool.and_true]; rfl

theorem tcall_okP {j : Nat} {ts : List (String × Prog isa)} (h : FnsOk ts) : OkP (Cfg.tcall j ts) :=
  okP_seq rfl (icalls_okP h)

/-- The code's blocks of the curve, with the functions it calls and the
bound on candidates of `cfgC`'s, which each curve's `RfcT` is of. -/
abbrev strip (c : Cfg) : Cfg := { c with f := ⟨[], [], []⟩, tries := 8, coreN := "", coreC := .block [] }

theorem cpLoop_okP : OkP Cfg.cpLoop := rfl

variable {c : Cfg} (hT : RfcT (strip c)) (hf : FnsOk c.f.init ∧ FnsOk c.f.upd ∧ FnsOk c.f.fin)
include hf

theorem initK_okP : OkP c.initK := okP_seq rfl (tcall_okP hf.1)

theorem updV_okP : OkP c.updV := okP_seq rfl (tcall_okP hf.2.1)

theorem updM_okP (len : Nat) : OkP (c.updM len) := okP_seq rfl (tcall_okP hf.2.1)

theorem fin_okP (len dst : Nat) : OkP (c.fin len dst) := okP_seq rfl (tcall_okP hf.2.2)

theorem hmacVS_okP : OkP c.hmacVS :=
  okP_seq (initK_okP hf) (okP_seq (by rfl) (okP_seq (updV_okP hf) (fin_okP hf _ _)))

theorem hmacVR_okP : OkP c.hmacVR := okP_seq (by rfl) (okP_seq (updV_okP hf) (fin_okP hf _ _))

theorem hmacK_okP (fresh : Bool) (len : Nat) : OkP (c.hmacK fresh len) := by
  unfold Cfg.hmacK
  refine okP_seq ?_ (okP_seq (updV_okP hf) (okP_seq (updM_okP hf _) (fin_okP hf _ _)))
  cases fresh
  · exact by rfl
  · exact initK_okP hf

include hT

theorem rekeyFull_okP (b : Nat) (hb : b < 2) : OkP (c.rekeyFull b) := by
  unfold Cfg.rekeyFull
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact okP_seq rfl (okP_seq (by exact hT.iMsgF₀) (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))
  · exact okP_seq rfl (okP_seq (by exact hT.iMsgF₁) (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))

omit hT in
theorem rekey_okP : OkP c.rekey :=
  okP_seq rfl (okP_seq (by simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]; rfl)
    (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))

omit hf in
theorem candTop_okP : OkP c.candTop := by
  unfold Cfg.candTop
  split
  · exact okP_seq rfl (by exact hT.iConvT)
  · rfl

theorem cand_okP : OkP c.cand :=
  okP_seq rfl (okP_seq (okP_loop (okP_seq (hmacVR_okP hf) (okP_seq rfl (okP_seq cpLoop_okP (by exact hT.iTStep)))))
    (candTop_okP hT))

theorem tryOne_okP (hcore : OkP c.coreC) : OkP c.tryOne :=
  okP_seq (cand_okP hT hf) (okP_seq (by exact hT.iCoreArgs) (okP_seq (okP_call hcore) (okP_seq rfl
    (okP_ite (okP_seq (rekey_okP hf) rfl) rfl))))

omit hf in
theorem prepH_okP : OkP c.prepH := by
  unfold Cfg.prepH
  split
  · exact okP_seq (by exact hT.iXcArgs) (okP_seq cpLoop_okP (okP_seq rfl (by exact hT.iConvC)))
  · exact by exact hT.iReduce

/-- The frame's body: no instruction writes a callee-saved SIMD register. -/
theorem body_okP (hcore : OkP c.coreC) : OkP c.body :=
  okP_seq rfl (okP_seq (okP_seq (by exact hT.iXArgs) cpLoop_okP) (okP_seq (prepH_okP hT) (okP_seq rfl
    (okP_seq (rekeyFull_okP hT hf 0 (by decide)) (okP_seq (rekeyFull_okP hT hf 1 (by decide)) (okP_seq rfl
      (okP_seq (okP_loop (tryOne_okP hT hf hcore)) rfl)))))))

/-- The whole function: its entry, and the frames' pushes and pops. -/
theorem sign_okP (hcore : OkP c.coreC) : OkP (signCode c) := by
  have hb := body_okP hT hf hcore
  refine okP_seq rfl ?_
  simp only [OkP, Cfg.sign, Code.allInstrs, hb, Bool.and_true]
  rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64
