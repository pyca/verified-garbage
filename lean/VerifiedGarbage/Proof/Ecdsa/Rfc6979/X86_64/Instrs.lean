module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Stack

/-!
# Deterministic ECDSA on x86-64: no instruction writes `rsp` or loads MXCSR

For code `c` (`Impl.Ecdsa.Rfc6979.X86_64.Cfg`) whose blocks of the curve's
and the hash function's sizes have neither (`RfcT`, which each curve's file
checks), whose table's functions have neither (`FnsGood`) and whose `core`
has neither: the frame's body (`body_okI`), and so the whole function.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.RsaOaep.X86_64 (okI)
open VG.Proof.RsaOaep.X86_64.Table (FnsGood icalls_good)

/-- Neither in `x`. -/
abbrev OkP (x : Prog isa) : Prop := x.allInstrs okI = true

theorem okP_seq {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.seq a b) := by
  show (a.allInstrs okI && b.allInstrs okI) = true; rw [ha, hb]; rfl

theorem okP_ite {cnd : Cond} {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.ite cnd a b) := by
  show (a.allInstrs okI && b.allInstrs okI) = true; rw [ha, hb]; rfl

theorem okP_loop {cnd : Cond} {a : Prog isa} (ha : OkP a) : OkP (.loop a cnd) := ha

theorem okP_call {n : String} {a : Prog isa} (ha : OkP a) : OkP (.call n a) := ha

theorem okP_block {is : List Instr} (h : OkB is) : OkP (.block is) := h

theorem tcall_okP {c : Cfg} {j : Nat} {ts : List (String × Prog isa)} (h : FnsGood ts) : OkP (c.tcall j ts) :=
  okP_seq rfl (okP_seq rfl (icalls_good h).1)

variable {c : Cfg} (hT : RfcT c) (hf : FnsGood c.f.init ∧ FnsGood c.f.upd ∧ FnsGood c.f.fin)
include hf

theorem initCall_okP (o : Nat) : OkP (c.initCall o) := okP_seq rfl (tcall_okP hf.1)

theorem updCall_okP (o cnt : Nat) {dataA : List Instr}
    (hd : (∃ a, dataA = Cfg.scr .rdx a) ∨ (∃ a, dataA = Cfg.fr .rdx a)) (len : Nat) :
    OkP (c.updCall o cnt dataA len) := by
  refine okP_seq ?_ (tcall_okP hf.2.1)
  rcases hd with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rfl
  · rfl

theorem finCall_okP (o cnt : Nat) : OkP (c.finCall o cnt) := okP_seq rfl (tcall_okP hf.2.2)

include hT

theorem hinit_okP : OkP c.hinit :=
  okP_seq (initCall_okP hf _) (okP_seq (initCall_okP hf _) (okP_seq hT.iPadI (okP_seq
    (updCall_okP hf _ _ (.inl ⟨_, rfl⟩) _) (okP_seq hT.iPadO (updCall_okP hf _ _ (.inl ⟨_, rfl⟩) _)))))

theorem hfin_okP (len : Nat) {dst : Nat} (hd : dst = fK ∨ dst = fV) : OkP (c.hfin len dst) :=
  okP_seq (finCall_okP hf _ _) (okP_seq (updCall_okP hf _ _ (.inl ⟨_, rfl⟩) _)
    (okP_seq (finCall_okP hf _ _) (by rcases hd with rfl | rfl; exacts [hT.iCopyK, hT.iCopyV])))

section Mac

variable {dataA : List Instr} (hd : (∃ a, dataA = Cfg.scr .rdx a) ∨ (∃ a, dataA = Cfg.fr .rdx a)) (len : Nat)
  {dst : Nat} (hdst : dst = fK ∨ dst = fV)
include hd hdst

theorem hmac_okP : OkP (c.hmac dataA len dst) :=
  okP_seq (hinit_okP hT hf) (okP_seq (updCall_okP hf _ _ hd _) (hfin_okP hT hf _ hdst))

theorem hmacS_okP : OkP (c.hmacS dataA len dst) :=
  okP_seq (hinit_okP hT hf) (okP_seq (by rfl)
    (okP_seq (updCall_okP hf _ _ hd _) (hfin_okP hT hf _ hdst)))

theorem hmacR_okP : OkP (c.hmacR dataA len dst) :=
  okP_seq (by rfl) (okP_seq (updCall_okP hf _ _ hd _) (hfin_okP hT hf _ hdst))

end Mac

theorem hmacVS_okP : OkP c.hmacVS := hmacS_okP hT hf (.inr ⟨_, rfl⟩) _ (.inr rfl)

theorem hmacVR_okP : OkP c.hmacVR := hmacR_okP hT hf (.inr ⟨_, rfl⟩) _ (.inr rfl)

theorem rekeyFull_okP (b : Nat) (hb : b < 2) : OkP (c.rekeyFull b) := by
  unfold Cfg.rekeyFull
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact okP_seq rfl (okP_seq hT.iMsgF₀ (okP_seq (hmac_okP hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_okP hT hf)))
  · exact okP_seq rfl (okP_seq hT.iMsgF₁ (okP_seq (hmacR_okP hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_okP hT hf)))

theorem rekey_okP : OkP c.rekey :=
  okP_seq rfl (okP_seq hT.iMsgN (okP_seq (hmac_okP hT hf (.inl ⟨_, rfl⟩) _ (.inl rfl)) (hmacVS_okP hT hf)))

theorem candW_okP : ∀ k, k ≤ 8 → OkP (c.candW k)
  | 0, _ => rfl
  | k + 1, hk => okP_seq (candW_okP k (by omega)) (okP_seq (hmacVR_okP hT hf) (hT.iKeepV k (by omega)))

theorem cand_okP : OkP c.cand := by
  unfold Cfg.cand
  split
  · exact okP_seq (candW_okP hT hf _ hT.m8) hT.iCandTop
  · exact hmacVR_okP hT hf

theorem tryOne_okP (hcore : OkP c.coreC) : OkP c.tryOne :=
  okP_seq (cand_okP hT hf) (okP_seq hT.iCoreArgs (okP_seq (okP_call hcore) (okP_seq rfl
    (okP_ite (okP_seq (rekey_okP hT hf) rfl) rfl))))

/-- The frame's body: no instruction writes `rsp` or loads MXCSR. -/
theorem body_okP (hcore : OkP c.coreC) : OkP c.body :=
  okP_seq hT.iDigestPtr (okP_seq hT.iPrep (okP_seq (rekeyFull_okP hT hf 0 (by decide))
    (okP_seq (rekeyFull_okP hT hf 1 (by decide)) (okP_seq rfl (okP_seq (okP_loop (tryOne_okP hT hf hcore))
      hT.iWipe)))))

end VG.Proof.Ecdsa.Rfc6979.X86_64
