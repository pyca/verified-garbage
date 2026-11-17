module

public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.Xdh.Arm
public import VerifiedGarbage.Proof.X25519.Arm.Verified
public import VerifiedGarbage.Proof.X25519.Arm.Words.Verified
import VerifiedGarbage.Proof.X25519.Arm.Lit
public import VerifiedGarbage.Spec.X25519.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X25519.Bytes
meta import VerifiedGarbage.Proof.Xdh.Arm
meta import VerifiedGarbage.Proof.X25519.Arm.Verified
meta import VerifiedGarbage.Proof.X25519.Arm.Words.Verified
meta import VerifiedGarbage.Proof.X25519.Arm.Lit
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.X25519.Bytes
meta import VerifiedGarbage.Proof.X25519.Contract

/-!
# X25519 exchange, with RFC 7748's check, on ARMv7

Untrusted: everything here is checked by Lean. Each implementation of
`vg_x25519` is a callee of `Impl.Xdh.Arm.exchange` by its shared contract
(`callee`), so `vg_x25519_exchange`, which calls it and checks its result
(`Proof/Xdh/Arm.lean`), is `Verified` against its shared contract, with the
8 bytes of stack its frames use.
-/

@[expose] public section

namespace VG.Proof.X25519.Arm.Exchange

open VG VG.Arm VG.Proof.Xdh.Arm

theorem callee {c : Prog isa} (hv : Verified Arm.target c (Proof.X25519.x25519Contract Arm.abi))
    (hn : c.noFrames = true) : Callee 32 4096 Spec.X25519.x25519 c (Proof.X25519.x25519Contract Arm.abi) where
  hv := hv.1
  hct := hv.2.1
  pre s h := by
    obtain ⟨rd, wr, d1, d2, d3, d4, d5, b0, b1, b2, b3⟩ := h
    sig_pre [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr, List.getD]
    sig_and_intros
    all_goals first
      | with_reducible assumption
      | trivial
      | omega_using []
      | exact Region.Disjoint.symm ‹_›
  post s s' h := by
    sig_post [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr] at h
    exact h
  pub s₁ s₂ h := by
    obtain ⟨q0, q1, q2, q3, qsp⟩ := h
    sig_pub [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_reduce [Proof.X25519.x25519Contract, Proof.X25519.x25519Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
      Arm.State.addr]
    sig_and_intros
    all_goals first | with_reducible assumption | trivial
  nf := hn

/-- `vg_x25519_exchange` calling `c`, an implementation of `vg_x25519`, as `name`. -/
theorem exchange_verified {c : Prog isa} (name : String)
    (hv : Verified Arm.target c (Proof.X25519.x25519Contract Arm.abi)) (hn : c.noFrames = true)
    (ht : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 32)) hc).isSome = true) :
    Verified Arm.target (Impl.Xdh.Arm.exchange name c 32) (Spec.X25519.exchangeContract Arm.abi 8) :=
  Verified.of_correct (k := exContract 32 4096 Spec.X25519.x25519) (exchange_correct (callee hv hn) (by decide))
    (exchange_ct (callee hv hn) ht) (by
      contract_implies [Spec.X25519.exchangeContract, Spec.X25519.exchangeSig, Proof.X25519.x25519Sig,
        exContract, ExPre, CallPre, ExPost, Pub, Proof.Xdh.Arm.outR, Proof.Xdh.Arm.scR, Proof.Xdh.Arm.ptR, Proof.Xdh.Arm.wsR,
        Proof.Xdh.Arm.frR, ret32, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val,
        Arm.State.addr] [Proof.X25519.Arm.x25519Sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using Proof.X25519.Arm.x25519Sat)

/-- The taint analysis of the check. -/
theorem check_taint : ∃ hc, (taint.check (Taint.ofRegs [.r1]) (.block (Impl.Xdh.Arm.check 32)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem exchange_baseline :
    Verified Arm.target (Impl.Xdh.Arm.exchange "vg_x25519" Impl.X25519.Arm.x25519 32)
      (Spec.X25519.exchangeContract Arm.abi 8) :=
  exchange_verified _ Proof.X25519.Arm.x25519_verified (by lit_decide) check_taint

theorem exchange_umaal :
    Verified Arm.target (Impl.Xdh.Arm.exchange "vg_x25519_umaal" Impl.X25519.Arm.Words.x25519Umaal 32)
      (Spec.X25519.exchangeContract Arm.abi 8) :=
  exchange_verified _ Proof.X25519.Arm.Words.x25519Umaal_verified (by lit_decide) check_taint

/-! ## `vg_x25519_base_umaal`

`X25519(k, 9)` by `vg_x25519_umaal` (`Impl/X25519/Arm/Words.lean`): the
setup writes the u-coordinate 9 past the callee's working space and saves
`r4` and `lr` after it (`setMem`), the callee is called by its shared
contract (`callee`) with that point, and `lr` and `r4` are loaded back from
bytes the callee does not write. -/

namespace BaseU

open VG.Impl.X25519.Arm.Words (BP baseSetup baseFinish x25519BaseUmaal x25519Umaal)
open VG.Spec.X25519 (bytesAt)
open VG.Proof.MdStream.Arm (Upd wp_ldr)

/-- `vg_x25519_base_umaal`'s contract on ARMv7. -/
def baseULocal : Contract isa where
  pre s :=
    s.rd = [⟨State.addr (s.gpr .r1), 32⟩] ∧
      s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩] ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩ ∧
      (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩ ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32
  post s t := bytesAt t.mem (State.addr (s.gpr .r0)) 32 =
    Spec.X25519.x25519 (bytesAt s.mem (State.addr (s.gpr .r1)) 32) Spec.X25519.basePoint
  pub s t := s.gpr .r0 = t.gpr .r0 ∧ s.gpr .r1 = t.gpr .r1 ∧ s.gpr .r2 = t.gpr .r2 ∧ s.sp = t.sp

/-- The precondition, by name. -/
structure Pre (s : State) : Prop where
  rd : s.rd = [⟨State.addr (s.gpr .r1), 32⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 8192⟩]
  out_sc : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r1), 32⟩
  out_ws : (⟨State.addr (s.gpr .r0), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  sc_ws : (⟨State.addr (s.gpr .r1), 32⟩ : Region).Disjoint ⟨State.addr (s.gpr .r2), 8192⟩
  f0 : (s.gpr .r0).toNat + 32 ≤ 2 ^ 32
  f1 : (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  f2 : (s.gpr .r2).toNat + 8192 ≤ 2 ^ 32

theorem Pre.of {s : State} (h : baseULocal.pre s) : Pre s :=
  let ⟨a, b, c, d, e, f, g, i⟩ := h
  ⟨a, b, c, d, e, f, g, i⟩

/-- The point's address: byte `BP` of `scratch`. -/
abbrev P32 (s : State) : BitVec 32 := s.gpr .r2 + 4096
abbrev PA (s : State) : Addr := State.addr (s.gpr .r2) + BitVec.ofNat 64 4096

/-- The memory after the setup: `r4` and `lr` saved, and the u-coordinate 9. -/
def setMem (s : State) : Mem :=
  ((((((((((s.mem.writeW (PA s + BitVec.ofNat 64 36) (s.gpr .r4)).writeW (PA s + BitVec.ofNat 64 32)
    (s.gpr .lr)).writeW (PA s + BitVec.ofNat 64 0) (9 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 4)
    (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 8) (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 12)
    (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 16) (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 20)
    (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 24) (0 : BitVec 32)).writeW (PA s + BitVec.ofNat 64 28)
    (0 : BitVec 32))

/-- A word read after a store of a word elsewhere at the point. -/
theorem rd_sep (m : Mem) (p : Addr) (v : BitVec 32) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d)
    (hd : d + 4 ≤ 64) (he : e + 4 ≤ 64) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 = m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep p h (by omega_using [hd]) (by omega_using [he])) (by decide)

theorem rd_self (m : Mem) (a : Addr) (v : BitVec 32) : (m.writeW a v).readW a 32 = v :=
  Mem.readW_writeW_self32 _ _ _

theorem setMem_frame (s : State) : Frame [⟨PA s, 40⟩] s.mem (setMem s) := by
  have c (d : Nat) (hd : d + 4 ≤ 40) : (⟨PA s, 40⟩ : Region).Contains (PA s + BitVec.ofNat 64 d) 4 :=
    Offset.contains_base _ hd (by omega_using [hd])
  have m : (⟨PA s, 40⟩ : Region) ∈ [(⟨PA s, 40⟩ : Region)] := List.mem_singleton_self _
  have f₁ := (Frame.refl [(⟨PA s, 40⟩ : Region)] s.mem).writeW m (s.gpr .r4) (c 36 (by decide))
  have f₂ := f₁.writeW m (s.gpr .lr) (c 32 (by decide))
  have f₃ := f₂.writeW m (9 : BitVec 32) (c 0 (by decide))
  have f₄ := f₃.writeW m (0 : BitVec 32) (c 4 (by decide))
  have f₅ := f₄.writeW m (0 : BitVec 32) (c 8 (by decide))
  have f₆ := f₅.writeW m (0 : BitVec 32) (c 12 (by decide))
  have f₇ := f₆.writeW m (0 : BitVec 32) (c 16 (by decide))
  have f₈ := f₇.writeW m (0 : BitVec 32) (c 20 (by decide))
  have f₉ := f₈.writeW m (0 : BitVec 32) (c 24 (by decide))
  exact f₉.writeW m (0 : BitVec 32) (c 28 (by decide))

theorem setMem_lr (s : State) : (setMem s).readW (PA s + BitVec.ofNat 64 32) 32 = s.gpr .lr := by
  simp (disch := decide) only [setMem, rd_sep, rd_self]

theorem setMem_r4 (s : State) : (setMem s).readW (PA s + BitVec.ofNat 64 36) 32 = s.gpr .r4 := by
  simp (disch := decide) only [setMem, rd_sep, rd_self]

/-- The point the setup writes is the base point's u-coordinate. -/
theorem setMem_point (s : State) : bytesAt (setMem s) (PA s) 32 = Spec.X25519.basePoint := by
  rw [show Spec.X25519.basePoint = Proof.X25519.leBytes 32 9 by decide]
  apply Proof.X25519.bytesAt_leBytes_words32
  intro j hj
  rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := decide) only [setMem, Nat.reduceMul, rd_sep, rd_self]
    decide

/-- What the setup leaves. -/
structure Setup (s e : State) : Prop where
  r0 : e.gpr .r0 = s.gpr .r0
  r1 : e.gpr .r1 = s.gpr .r1
  r2 : e.gpr .r2 = P32 s
  r3 : e.gpr .r3 = s.gpr .r2
  r4 : e.gpr .r4 = P32 s
  keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → e.gpr r = s.gpr r
  sp : e.sp = s.sp
  rd : e.rd = s.rd
  wr : e.wr = s.wr
  mem : e.mem = setMem s

theorem pA {s : State} (h : Pre s) (d : Nat) (hd : d < 4096) :
    State.addr (s.gpr .r2 + 4096 + BitVec.ofNat 32 d) = PA s + BitVec.ofNat 64 d := by
  have f2 := h.f2
  have e : (s.gpr .r2 + 4096 : BitVec 32) = s.gpr .r2 + BitVec.ofNat 32 4096 := rfl
  rw [e, addr_add (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [f2, hd]), addr_add (by omega_using [f2])]

theorem inWs {s : State} (d : Nat) (hd : d + 4 ≤ 4096) :
    (⟨State.addr (s.gpr .r2), 8192⟩ : Region).Contains (PA s + BitVec.ofNat 64 d) 4 := by
  show Region.Contains _ (State.addr (s.gpr .r2) + BitVec.ofNat 64 4096 + BitVec.ofNat 64 d) 4
  rw [Offset.add_add]
  exact Offset.contains_base _ (by omega_using [hd]) (by omega_using [hd])

theorem setup_wp {s : State} (h : Pre s) : WP isa (.block baseSetup) s (Setup s) := by
  have i0 (t : State) : (Op2.imm 0).eval t = some 0 := Proof.MdStream.Arm.op2_imm (by decide)
  have i9 (t : State) : (Op2.imm 9).eval t = some 9 := Proof.MdStream.Arm.op2_imm (by decide)
  have i4096 (t : State) : (Op2.imm 4096).eval t = some 4096 := Proof.MdStream.Arm.op2_imm (by decide)
  have w (d : Nat) (hd : d + 4 ≤ 4096) : InRegions s.wr (PA s + BitVec.ofNat 64 d) 4 := by
    rw [h.wr]; exact ⟨_, by simp, inWs d hd⟩
  refine WP.of_runBlock ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, baseSetup, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
      i0, i9, i4096, Proof.MdStream.Arm.op2_reg, State.store32, Option.map_some, Nat.reduceLT,
      VG.Arm.RegUpd.gpr_setReg, VG.Arm.RegUpd.mem_setReg, VG.Arm.RegUpd.rd_setReg, VG.Arm.RegUpd.wr_setReg,
      pA h 0 (by decide), pA h 4 (by decide), pA h 8 (by decide), pA h 12 (by decide), pA h 16 (by decide),
      pA h 20 (by decide), pA h 24 (by decide), pA h 28 (by decide), pA h 32 (by decide), pA h 36 (by decide),
      w 0 (by decide), w 4 (by decide), w 8 (by decide), w 12 (by decide), w 16 (by decide), w 20 (by decide),
      w 24 (by decide), w 28 (by decide), w 32 (by decide), w 36 (by decide)]
    rfl, ?_⟩
  exact ⟨by simp [VG.Arm.RegUpd.gpr_setReg], by simp [VG.Arm.RegUpd.gpr_setReg], by simp [VG.Arm.RegUpd.gpr_setReg, P32],
    by simp [VG.Arm.RegUpd.gpr_setReg], by simp [VG.Arm.RegUpd.gpr_setReg, P32],
    fun r h2 h3 h4 h12 => by simp [VG.Arm.RegUpd.gpr_setReg, h2, h3, h4, h12], rfl, rfl, rfl, rfl⟩

/-- The regions the callee is given. -/
abbrev cRd (s : State) : List Region := [⟨State.addr (s.gpr .r1), 32⟩, ⟨State.addr (P32 s), 32⟩]
abbrev cWr (s : State) : List Region := [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r2), 4096⟩]

theorem p32A {s : State} (h : Pre s) : State.addr (P32 s) = PA s := by
  have f2 := h.f2
  show State.addr (s.gpr .r2 + BitVec.ofNat 32 4096) = _
  exact addr_add (by omega_using [f2])

theorem P32_fit {s : State} (h : Pre s) : (P32 s).toNat + 32 ≤ 2 ^ 32 := by
  have f2 := h.f2
  have e : (s.gpr .r2 + 4096 : BitVec 32) = s.gpr .r2 + BitVec.ofNat 32 4096 := rfl
  rw [P32, e, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_using [f2]

theorem ptSub (s : State) : Region.Sub ⟨PA s, 40⟩ ⟨State.addr (s.gpr .r2), 8192⟩ := Offset.sub_base _ (by decide)

/-- The callee's entry. -/
theorem Setup.callPre {s e : State} (h : Pre s) (he : Setup s e) :
    CallPre 32 4096 (e.callEntry.withRegions (cRd s) (cWr s)) := by
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2, .r3]) :
      (e.callEntry.withRegions (cRd s) (cWr s)).gpr r = e.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]
  have pt : Region.Sub ⟨PA s, 32⟩ ⟨State.addr (s.gpr .r2), 8192⟩ := Offset.sub_base _ (by decide)
  simp only [CallPre, outR, scR, ptR, wsR, State.withRegions_rd, State.withRegions_wr,
    g .r0 (by simp), g .r1 (by simp), g .r2 (by simp), g .r3 (by simp), he.r0, he.r1, he.r2, he.r3]
  refine ⟨trivial, trivial, h.out_sc, ?_, h.out_ws.sub_right (Region.sub_prefix (by decide)),
    h.sc_ws.sub_right (Region.sub_prefix (by decide)), ?_, h.f0, h.f1, P32_fit h, by have := h.f2; omega_using [this]⟩
  · rw [p32A h]; exact h.out_ws.sub_right pt
  · rw [p32A h]; exact Offset.disjoint_base _ (by decide) (by decide)

theorem Setup.covers {s e : State} (h : Pre s) (he : Setup s e) :
    Covers (cRd s ++ cWr s) (e.rd ++ e.wr) ∧ Covers (cWr s) e.wr := by
  rw [he.rd, he.wr, h.rd, h.wr]
  unfold cRd cWr
  rw [p32A h]
  constructor
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr (s.gpr .r1), 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨State.addr (s.gpr .r2), 8192⟩, by simp, 4096, rfl, by simp⟩
    · exact ⟨⟨State.addr (s.gpr .r0), 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨State.addr (s.gpr .r2), 8192⟩, by simp, 0, by simp, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨State.addr (s.gpr .r0), 32⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨State.addr (s.gpr .r2), 8192⟩, by simp, 0, by simp, by simp⟩

/-- What the call leaves. -/
structure Called (s z : State) : Prop where
  out : bytesAt z.mem (State.addr (s.gpr .r0)) 32 =
    Spec.X25519.x25519 (bytesAt s.mem (State.addr (s.gpr .r1)) 32) Spec.X25519.basePoint
  r4 : z.gpr .r4 = P32 s
  keep : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r4 → z.gpr r = s.gpr r
  lr : z.mem.readW (PA s + BitVec.ofNat 64 32) 32 = s.gpr .lr
  sv : z.mem.readW (PA s + BitVec.ofNat 64 36) 32 = s.gpr .r4
  sp : z.sp = s.sp
  rd : z.rd = s.rd
  wr : z.wr = s.wr

theorem bytes_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  unfold bytesAt
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem called_wp {c : Prog isa} {k : Contract isa} (hk : Callee 32 4096 Spec.X25519.x25519 c k) {name : String}
    {s e : State} (h : Pre s) (he : Setup s e) : WP isa (.call name c) e (Called s) := by
  have hcp := he.callPre h
  obtain ⟨hcov, hw⟩ := he.covers h
  refine WP.callCalls hk.hv (hk.pre _ hcp) hcov hw (fun z rd' wr' sp' fr' pres' _ post' => ?_) hk.nf
  have hpost := hk.post _ _ post'
  have g (r : Reg) (hr : r ∈ [Reg.r0, .r1, .r2]) : (e.callEntry.withRegions (cRd s) (cWr s)).gpr r = e.gpr r := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]
  simp only [State.withRegions_mem, State.callEntry_mem, g .r0 (by simp), g .r1 (by simp), g .r2 (by simp),
    he.r0, he.r1, he.r2, he.mem, p32A h, setMem_point] at hpost
  have sc : bytesAt (setMem s) (State.addr (s.gpr .r1)) 32 = bytesAt s.mem (State.addr (s.gpr .r1)) 32 :=
    bytes_frame (setMem_frame s) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact h.sc_ws.sub_right (ptSub s)) (by decide)
  rw [sc] at hpost
  -- The saved words, which the callee does not write.
  have apart {d : Nat} (hd : 32 ≤ d) (hd' : d + 4 ≤ 40) :
      ∀ r ∈ cWr s, (⟨PA s + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine (h.out_ws.sub_right ?_).symm
      show Region.Sub ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 4096 + BitVec.ofNat 64 d, 4⟩ _
      rw [Offset.add_add]
      exact Offset.sub_base _ (by omega_using [hd'])
    · show Region.Disjoint ⟨State.addr (s.gpr .r2) + BitVec.ofNat 64 4096 + BitVec.ofNat 64 d, 4⟩ _
      rw [Offset.add_add]
      exact Offset.disjoint_base _ (by omega_using [hd]) (by omega_using [hd'])
  refine ⟨hpost, by rw [pres' .r4 (by simp [preserved]) (by decide), he.r4],
    fun r hr hlr h4 => ?_, ?_, ?_, sp'.trans he.sp, rd'.trans he.rd, wr'.trans he.wr⟩
  · rw [pres' r hr hlr]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hlr
      | exact absurd rfl h4
      | exact he.keep _ (by decide) (by decide) (by decide) (by decide)
  · rw [Frame.readW fr' (r := ⟨PA s + BitVec.ofNat 64 32, 4⟩) (Region.contains_self _ _)
      (apart (by decide) (by decide)) (by decide), he.mem, setMem_lr]
  · rw [Frame.readW fr' (r := ⟨PA s + BitVec.ofNat 64 36, 4⟩) (Region.contains_self _ _)
      (apart (by decide) (by decide)) (by decide), he.mem, setMem_r4]

theorem finish_wp {s z : State} (h : Pre s) (hz : Called s z) :
    WP isa (.block baseFinish) z fun t => abiPreserved s t ∧ baseULocal.post s t := by
  have inR (d : Nat) (hd : d + 4 ≤ 4096) : InRegions (z.rd ++ z.wr) (PA s + BitVec.ofNat 64 d) 4 := by
    rw [hz.rd, hz.wr, h.rd, h.wr]; exact ⟨⟨State.addr (s.gpr .r2), 8192⟩, by simp, inWs d hd⟩
  rw [show baseFinish = [.ldr .lr .r4 32, .ldr .r4 .r4 36] from rfl]
  refine wp_ldr (a := PA s + BitVec.ofNat 64 32) (by decide) (by rw [hz.r4]; exact pA h 32 (by decide))
    (inR 32 (by decide)) fun u hu => ?_
  refine wp_ldr (a := PA s + BitVec.ofNat 64 36) (by decide)
    (by rw [hu.other _ (by decide), hz.r4]; exact pA h 36 (by decide))
    (by rw [hu.rd, hu.wr]; exact inR 36 (by decide)) fun t ht => WP.block_nil ?_
  refine ⟨⟨fun r hr => ?_, by rw [ht.sp, hu.sp, hz.sp]⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4; rw [ht.gpr, hu.mem, hz.sv]
    · by_cases hl : r = .lr
      · subst hl; rw [ht.other _ (by decide), hu.gpr, hz.lr]
      · rw [ht.other _ h4, hu.other _ hl, hz.keep r hr hl h4]
  · show bytesAt t.mem _ 32 = _
    rw [ht.mem, hu.mem]; exact hz.out

theorem base_correct {c : Prog isa} {k : Contract isa} (hk : Callee 32 4096 Spec.X25519.x25519 c k)
    (name : String) (s : State) (hs : baseULocal.pre s) :
    WP isa (.seq (.block baseSetup) (.seq (.call name c) (.block baseFinish))) s fun t =>
      abiPreserved s t ∧ baseULocal.post s t := by
  have h := Pre.of hs
  exact WP.seq (WP.mono (setup_wp h) fun _ he =>
    WP.seq (WP.mono (called_wp hk h he) fun _ hz => finish_wp h hz))

/-! ### Constant time -/

theorem setup_taint : ∃ hc, (taint.check (Taint.ofRegs [.r0, .r1, .r2]) (.block baseSetup) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem finish_taint : ∃ hc, (taint.check (Taint.ofRegs [.r4]) (.block baseFinish) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem base_rel {c : Prog isa} {k : Contract isa} (hk : Callee 32 4096 Spec.X25519.x25519 c k) (name : String)
    {s₀ s₀' : State} (h0 : baseULocal.pre s₀) (h0' : baseULocal.pre s₀') (hq : baseULocal.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (.seq (.block baseSetup) (.seq (.call name c) (.block baseFinish)))
      fun _ _ => True := by
  have hp := Pre.of h0
  have hp' := Pre.of h0'
  obtain ⟨q0, q1, q2, qsp⟩ := hq
  have qP : P32 s₀ = P32 s₀' := by rw [P32, P32, q2]
  have r₁ := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := Setup s₀) (G' := Setup s₀')
    (Taint.ofRegs [.r0, .r1, .r2]) (fun a b ea eb => Taint.agree_ofRegs fun r hr => by
      subst ea eb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact q0
      · exact q1
      · exact q2) setup_taint
    (fun s e => by rw [e]; exact setup_wp hp) (fun s e => by rw [e]; exact setup_wp hp')
  have r₂ := rel_wp (F := Setup s₀) (F' := Setup s₀') (G := Called s₀) (G' := Called s₀') (c := .call name c)
    (RelCT.call hk.hv hk.hct (cRd s₀) (cWr s₀) fun a b ⟨ha, hb⟩ => by
      have ca := ha.callPre hp
      have cb := hb.callPre hp'
      have cva := ha.covers hp
      have cvb := hb.covers hp'
      have eR : cRd s₀' = cRd s₀ := by rw [cRd, cRd, q1, qP]
      have eW : cWr s₀' = cWr s₀ := by rw [cWr, cWr, q0, q2]
      rw [eR, eW] at cb cvb
      refine ⟨hk.pre _ ca, hk.pre _ cb, hk.pub _ _ ⟨?_, ?_, ?_, ?_, ?_⟩, cva.1, cva.2, cvb.1, cvb.2⟩
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
          State.callEntry_gpr _ (by decide), ha.r0, hb.r0, q0]
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
          State.callEntry_gpr _ (by decide), ha.r1, hb.r1, q1]
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
          State.callEntry_gpr _ (by decide), ha.r2, hb.r2, qP]
      · rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
          State.callEntry_gpr _ (by decide), ha.r3, hb.r3, q2]
      · rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, ha.sp, hb.sp, qsp])
    (fun _ h => called_wp hk hp h) (fun _ h => called_wp hk hp' h)
  have r₃ := rel_agree (F := Called s₀) (F' := Called s₀') (G := fun _ => True) (G' := fun _ => True)
    (Taint.ofRegs [.r4]) (fun a b ha hb => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ha.r4, hb.r4, qP]) finish_taint
    (fun _ h => WP.mono (finish_wp hp h) fun _ _ => trivial)
    (fun _ h => WP.mono (finish_wp hp' h) fun _ _ => trivial)
  exact (r₁.seq (r₂.seq r₃)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-- A state satisfying the precondition. -/
def baseUSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x8000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x8000, 8192⟩]

/-- `vg_x25519_base_umaal`, calling `vg_x25519_umaal`. -/
theorem x25519BaseUmaal_verified :
    Verified Arm.target x25519BaseUmaal (Spec.X25519.x25519BaseContract Arm.abi) := by
  have hk := callee Proof.X25519.Arm.Words.x25519Umaal_verified (by lit_decide)
  have hc : ∀ s, baseULocal.pre s → ∃ t s', Exec isa x25519BaseUmaal s t s' ∧ abiPreserved s s' ∧
      baseULocal.post s s' := fun s hs => base_correct hk _ s hs
  have hct : ConstantTime isa baseULocal.pre baseULocal.pub x25519BaseUmaal :=
    fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (base_rel hk _ h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1
  exact Verified.of_correct (k := baseULocal) hc hct (by
    contract_implies [Spec.X25519.x25519BaseContract, Spec.X25519.x25519BaseSig, baseULocal, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [baseUSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using baseUSat)

end BaseU

end VG.Proof.X25519.Arm.Exchange
