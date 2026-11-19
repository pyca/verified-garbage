module

import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.NoSp
import VerifiedGarbage.Proof.MlKem.X86.Top
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.MlKem.X86.Top
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Framework.X86.NativeHintData
public import VerifiedGarbage.Proof.MlDsa.X86.Message.HashMu
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.HashMu
meta import VerifiedGarbage.Proof.MlKem.X86.TopCall
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Impl.MlDsa.X86.Message
public import VerifiedGarbage.Proof.MlDsa.X86.Message.Hash
public import VerifiedGarbage.Spec.MlDsa.CachedVerify
import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MlDsa.X86.Message.Hash
import VerifiedGarbage.Proof.Sha3.X86.Permute
meta import VerifiedGarbage.Proof.Sha3.X86.Permute
meta import VerifiedGarbage.Impl.MlDsa.X86.Message
meta import VerifiedGarbage.Spec.MlDsa.CachedVerify
meta import VerifiedGarbage.Proof.MlKem.X86.Piece
meta import VerifiedGarbage.Proof.MlKem.X86.Leaf
meta import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlDsa.X86.Message.SignCall`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86.Message.Shapes`, which only this module used -/

section

/-! ### `MlDsa.X86.Message.Entry`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the check, the entry and the leaf

Untrusted: everything here is checked by Lean. What both functions' proofs
need of their layouts (`Shape`): where the arguments are, and the facts
their preconditions give. After the leaf's push, the body loads `ctx_len`
and compares it with 256 (`chk_piece`); if it is larger it returns 2
(`ret2_piece`), and otherwise points `esi` at the 1 KiB and stores
`0 ‖ ctx_len` there (`enter_piece`), which is where `Ctx` starts; then the
rest of the body, in a leaf (`top_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.X86.Wp VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR P0_esp P0_wr P0_arg P0_argIn P0_argAddr LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa (Params)

/-- What the proofs need of the layouts of runs from states satisfying
`Pre`: the function's arguments, `scratch` among them (argument `si`), and
the facts the precondition gives. -/
structure Shape (Pre : State → Prop) (Pub : State → State → Prop) (lay : State → Lay) (si : Nat) (p : Params) :
    Prop where
  sp : ∀ s₀, Pre s₀ → (lay s₀).SP = E0 s₀
  rd : ∀ s₀, Pre s₀ → (lay s₀).rd = s₀.rd
  wr : ∀ s₀, Pre s₀ → (lay s₀).wr = s₀.wr
  argv : ∀ s₀, Pre s₀ → ∀ i < (lay s₀).nA, (lay s₀).argv.getD i 0 = arg s₀ i
  ctxLen : ∀ s₀, Pre s₀ → (lay s₀).ctxLen = arg s₀ 4
  scr : ∀ s₀, Pre s₀ → (lay s₀).scr = arg s₀ si
  siLt : ∀ s₀, Pre s₀ → si < (lay s₀).nA
  E : ∀ s₀, Pre s₀ → (lay s₀).E = oE p
  ok : ∀ s₀, Pre s₀ → (arg s₀ 4).toNat < 256 → (lay s₀).Ok
  e16 : ∀ s₀, Pre s₀ → 16 ≤ (E0 s₀).toNat ∧ (E0 s₀).toNat + 4 ≤ 2 ^ 32
  fit : ∀ s₀, Pre s₀ → (E0 s₀).toNat + 4 + 4 * (lay s₀).nA ≤ 2 ^ 32
  fd : ∀ s₀, Pre s₀ → (⟨(E0 s₀).setWidth 64 - 16#64, 16⟩ : Region).Disjoint ⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩
  ain : ∀ s₀, Pre s₀ → (⟨argAddr s₀ 0, 4 * (lay s₀).nA⟩ : Region) ∈ s₀.rd ++ s₀.wr
  n5 : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA
  pubE : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → E0 s₀ = E0 s₀'
  pubA : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → arg s₀ 4 = arg s₀' 4 ∧ arg s₀ si = arg s₀' si
  pubL : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀')

/-- `mov [b + o], r8` -/
theorem wp_st8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {si : Nat} {p : Params}

/-- After the check: `eax` is `ctx_len`, and the carry says whether it is below 256. -/
def Chk (s₀ s : State) : Prop :=
  Only [.eax] (P0 s₀) s ∧ s.cf = some (decide ((arg s₀ 4).toNat < 256))

theorem arg4_in (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (addr (E0 s₀ - 16) (20 + 4 * i)) 4 := by
  rw [← P0_esp]
  show InRegions _ (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 4
  rw [P0_argAddr]
  exact P0_argIn hi (hS.fit s₀ h₀) (hS.ain s₀ h₀)

theorem arg_P0 (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) {i : Nat} (hi : i < (lay s₀).nA) :
    (P0 s₀).mem.readW (addr (E0 s₀ - 16) (20 + 4 * i)) 32 = arg s₀ i := by
  rw [← P0_esp]
  show (P0 s₀).mem.readW (((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64) 32 = _
  rw [P0_argAddr]
  exact P0_arg (hS.e16 s₀ h₀).1 hi (hS.fit s₀ h₀) (hS.fd s₀ h₀)

theorem chk_piece (hS : Shape Pre Pub lay si p) :
    Piece Pre Pub (fun s₀ s => s = P0 s₀) Chk (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)]) := by
  refine Piece.taint [.esp] (fun s₀ s h₀ e => ?_) (fun s₀ s₀' s s' h₀ h₀' hq e e' r hr => ?_) (by native_taint_decide)
  · subst e
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega_using [this]
    refine wp_ldm (b := .esp) (P0_esp s₀) (arg4_in hS h₀ h4) fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil ?_
    refine ⟨⟨fun r hr => ?_, by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩, ?_⟩
    · rw [f₂.gpr, u₁.other r (by simpa using hr)]
    · rw [c₂, u₁.gpr, arg_P0 hS h₀ h4]; rfl
  · simp only [List.mem_singleton] at hr; subst hr
    rw [e, e', P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]

/-- `ctx_len ≥ 256`: return 2. -/
theorem ret2_piece {B : State → State → Prop}
    (hB : ∀ s₀ s, Pre s₀ → Only [.eax] (P0 s₀) s → 256 ≤ (arg s₀ 4).toNat → s.gpr .eax = 2 → B s₀ s) :
    Piece Pre Pub (fun s₀ s => Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = true) B
      (.block [.mov .eax (.imm 2)]) := by
  refine Piece.taint [] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => wp_movi fun s₁ u₁ => WP.block_nil ?_)
    (fun _ _ _ _ _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by native_taint_decide)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, Nat.not_lt] at hb
  refine hB s₀ s₁ h₀ ⟨fun r hr => ?_, by rw [u₁.mem, o.mem], by rw [u₁.rd, o.rd], by rw [u₁.wr, o.wr]⟩ hb u₁.gpr
  rw [u₁.other r (by simpa using hr), o.gpr r hr]

/-- Bytes `0 ‖ c` at `X + 944`, from their stores. -/
theorem hdr_bytes (m : Mem) (X : Addr) (c : BitVec 32) :
    bytesAt ((m.writeW (X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW (X + BitVec.ofNat 64 945)
      (c.setWidth 8)) (X + BitVec.ofNat 64 944) 2 = [0, BitVec.ofNat 8 c.toNat] := by
  have n45 : X + BitVec.ofNat 64 944 ≠ X + BitVec.ofNat 64 945 :=
    Offset.add_ofNat_ne _ (by omega_using []) (by omega_using []) (by omega_using [])
  simp only [bytesAt, List.range, List.range.loop, List.map_cons, List.map_nil, add_add, Nat.reduceAdd]
  rw [byte_writeW_other _ n45, byte_writeW_self, byte_writeW_self]
  refine List.cons_eq_cons.mpr ⟨rfl, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem E0_E1 (hS : Shape Pre Pub lay si p) {s₀ : State} (h₀ : Pre s₀) : E0 s₀ - 16 = (lay s₀).E1 := by
  rw [Lay.E1, hS.sp s₀ h₀]; rfl

/-- `esi ← scratch + oE p`, and `0 ‖ ctx_len` at `esi + 944`. -/
theorem enter_piece (hS : Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece Pre Pub (fun s₀ s => Chk s₀ s ∧ (!decide ((arg s₀ 4).toNat < 256)) = false) (CtxO lay) (enter si p) := by
  refine Piece.seq (B := fun s₀ s => Only [.eax, .esi] (P0 s₀) s ∧ s.gpr .esi = (lay s₀).X32 ∧ (lay s₀).Ok)
    (Piece.taint [.esp] (fun s₀ s h₀ ⟨⟨o, _⟩, hb⟩ => ?_) (fun s₀ s₀' s s' h₀ h₀' hq ⟨⟨o, _⟩, _⟩ ⟨⟨o', _⟩, _⟩ r hr => ?_) tt)
    (Piece.taint [.esp, .esi] (fun s₀ s h₀ ⟨o, hx, hL⟩ => ?_)
      (fun s₀ s₀' s s' h₀ h₀' hq ⟨o, hx, _⟩ ⟨o', hx', _⟩ r hr => ?_) (by native_taint_decide))
  · have hc : (arg s₀ 4).toNat < 256 := by simpa using hb
    have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have hin : InRegions (s.rd ++ s.wr) (addr (E0 s₀ - 16) (20 + 4 * si)) 4 := by
      rw [o.rd, o.wr]; exact arg4_in hS h₀ (hS.siLt s₀ h₀)
    refine wp_ldm (b := .esp) hsp hin fun s₁ u₁ => wp_addi fun s₂ u₂ => WP.block_nil
      ⟨⟨fun r hr => ?_, by rw [u₂.mem, u₁.mem, o.mem], by rw [u₂.rd, u₁.rd, o.rd], by rw [u₂.wr, u₁.wr, o.wr]⟩,
        ?_, hS.ok s₀ h₀ hc⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [u₂.other r hr.2, u₁.other r hr.2, o.gpr r (by simpa using hr.1)]
    · rw [u₂.gpr, u₁.gpr, o.mem, arg_P0 hS h₀ (hS.siLt s₀ h₀), Lay.X32, hS.scr s₀ h₀, hS.E s₀ h₀]
  · simp only [List.mem_singleton] at hr; subst hr
    rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
  · have hsp : s.gpr .esp = E0 s₀ - 16 := by rw [o.gpr _ (by decide), P0_esp]
    have h4 : 4 < (lay s₀).nA := by have := hS.n5 s₀ h₀; omega_using [this]
    have e944 : addr (lay s₀).X32 oHdr = (lay s₀).X + BitVec.ofNat 64 944 := hL.xo (by decide)
    have e945 : addr (lay s₀).X32 (oHdr + 1) = (lay s₀).X + BitVec.ofNat 64 945 := hL.xo (by decide)
    have hwr : s.wr = frameR s₀ :: (lay s₀).wr := by rw [o.wr, P0_wr, hS.wr s₀ h₀]
    have hout : ∀ e, e + 1 ≤ 1024 → InRegions s.wr ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he => by
      obtain ⟨R, hR, c⟩ := hL.inW (e := e) (k := 1) he
      exact ⟨R, by rw [hwr]; exact List.mem_cons_of_mem _ hR, c⟩
    have cSC : ∀ e, e + 1 ≤ 1024 → (lay s₀).SC.Contains ((lay s₀).X + BitVec.ofNat 64 e) 1 := fun e he =>
      hL.sub_sc (e := e) (k := 1) he _ (Region.contains_self _ _)
    refine wp_movi fun s₁ u₁ => wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₁.other _ (by decide), hx])
      (by rw [e944, u₁.wr]; exact hout 944 (by omega_using [])) fun s₂ m₂ => ?_
    have f₂ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₂.mem := by
      rw [m₂.mem, u₁.mem, o.mem, e944]
      exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (cSC 944 (by omega_using []))
    have hargs : ∀ {m : Mem}, Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem m → ∀ i < (lay s₀).nA,
        m.readW (((lay s₀).SP + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64) 32 = arg s₀ i := by
      intro m fr i hi
      rw [fr.readW (hL.argIn hi) (fun r hr => ?_) (by decide), ← Lay.Ok.argAt_eq, ← E0_E1 hS h₀]
      · exact arg_P0 hS h₀ hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hL.aSC
        · exact hL.kArgs.symm
    refine wp_ldm (b := .esp) (by rw [m₂.gpr, u₁.other _ (by decide), hsp])
      (by rw [m₂.rd, m₂.wr, u₁.rd, u₁.wr, o.rd, o.wr]; exact arg4_in hS h₀ h4) fun s₃ u₃ => ?_
    have v₃ : s₃.gpr .eax = arg s₀ 4 := by
      rw [u₃.gpr, E0_E1 hS h₀, Lay.Ok.argAt_eq]; exact hargs f₂ 4 h4
    refine wp_st8 (b := .esi) (B := (lay s₀).X32) (by rw [u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx])
      (by rw [e945, u₃.wr, m₂.wr, u₁.wr]; exact hout 945 (by omega_using [])) fun s₄ m₄ => WP.block_nil ⟨hL, ?_⟩
    have mm : s₄.mem = ((P0 s₀).mem.writeW ((lay s₀).X + BitVec.ofNat 64 944) ((0 : BitVec 32).setWidth 8)).writeW
        ((lay s₀).X + BitVec.ofNat 64 945) ((arg s₀ 4).setWidth 8) := by
      have ral : Reg8.al.reg = .eax := rfl
      rw [m₄.mem, u₃.mem, e945, m₂.mem, u₁.mem, o.mem, e944, ral, v₃, u₁.gpr]
    have f₄ : Frame [(lay s₀).SC, (lay s₀).STK] (P0 s₀).mem s₄.mem := by
      rw [m₄.mem, u₃.mem, e945]
      exact f₂.writeW (List.mem_cons_self ..) _ (cSC 945 (by omega_using []))
    refine ⟨by rw [m₄.rd, u₃.rd, m₂.rd, u₁.rd, o.rd, pushed_rd, hS.rd s₀ h₀],
      by rw [m₄.wr, u₃.wr, m₂.wr, u₁.wr, hwr, hS.sp s₀ h₀], by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr,
        u₁.other _ (by decide), hsp, E0_E1 hS h₀],
      by rw [m₄.gpr, u₃.other _ (by decide), m₂.gpr, u₁.other _ (by decide), hx],
      by rw [mm, hdr_bytes, hS.ctxLen s₀ h₀], fun i hi => by rw [hargs f₄ i hi, hS.argv s₀ h₀ i hi], f₄⟩
  · have hp := hS.pubL s₀ s₀' h₀ h₀' hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [o.gpr _ (by decide), o'.gpr _ (by decide), P0_esp, P0_esp, hS.pubE s₀ s₀' h₀ h₀' hq]
    · rw [hx, hx', hp.x]

/-- The whole function: the check, and the entry and `rest` if `ctx_len < 256`, in a leaf
that changes memory only within `W`. -/
theorem top_piece (hS : Shape Pre Pub lay si p) {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt si)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    {rest : Prog isa} {B : State → State → Prop} (W : State → List Region)
    (hW : ∀ s₀, Pre s₀ → ∀ r ∈ W s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r)
    (hsp : NoSp (.seq (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)])
      (.ite .ae (.block [.mov .eax (.imm 2)]) (.seq (enter si p) rest))))
    (hr : Piece Pre Pub (CtxO lay) (fun s₀ s => LeafEnd s₀ (W s₀) s ∧ B s₀ s) rest) :
    Piece Pre Pub (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ B s₀ s) s₀ s') (top (enter si p) rest) := by
  refine Piece.leaf W hsp hS.e16 hW hS.pubE ?_
  refine Piece.seq (chk_piece hS) (Piece.ite (fun s₀ => !decide ((arg s₀ 4).toNat < 256))
    (fun s₀ s h₀ h => ?_) (fun s₀ s₀' h₀ h₀' hq => ?_) (ret2_piece fun s₀ s h₀ o hc h2 => ?_)
    (Piece.seq (enter_piece hS tt) (hr.mono (fun _ _ _ h => h) fun s₀ s h₀ ⟨he, hb⟩ => ⟨he, .inr hb⟩)))
  · show s.cf.map (!·) = _
    rw [h.2]; rfl
  · rw [(hS.pubA s₀ s₀' h₀ h₀' hq).1]
  · exact ⟨⟨by rw [o.mem]; exact Frame.refl _ _, o.gpr _ (by decide), o.rd, o.wr⟩, .inl ⟨hc, h2⟩⟩

/-- `LeafEnd`, from `Ctx` and a frame of the memory from it. -/
theorem CtxO.leafEnd (hS : Shape Pre Pub lay si p) {s₀ s s' : State} (h₀ : Pre s₀) (hc : CtxO lay s₀ s)
    {W : List Region} (hW : ∀ r ∈ [(lay s₀).SC, (lay s₀).STK], r ∈ W) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hrs : ∀ r ∈ rs, ∃ R ∈ W, Region.Sub r R)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : LeafEnd s₀ W s' := by
  refine ⟨(hc.ctx.frame.sub fun r hr => ⟨r, hW r hr, fun _ h => h⟩).trans (hf.sub hrs),
    by rw [hsp, hc.ctx.esp, ← E0_E1 hS h₀, P0_esp], by rw [hrd, hc.ctx.rd, hS.rd s₀ h₀, pushed_rd],
    by rw [hwr, hc.ctx.wr, P0_wr, hS.wr s₀ h₀, hS.sp s₀ h₀]⟩

end

end VG.Proof.MlDsa.X86.Message

end

end

/-! ### `MlDsa.X86.Message.Pre`, which only this module used -/

section

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the preconditions and the layouts

Untrusted: everything here is checked by Lean. The functions on messages
take their key as a `KeyArg`: its length, and what their contracts require
of it (nothing of an encoded key; of a prepared one, that it is one), and
call a function on `μ` that takes the same key (`signKContract`,
`verifyKContract`). `signMessageKContract` and `verifyMessageKContract` are
the contracts of both kinds (`signMessageContract_eq`, …). Their
preconditions, with 176 and 172 bytes of stack, are spelled out (`SPre`,
`CPre`, which extends `VPre`), and so are the layouts of runs from states
satisfying them (`slay`, `vlay`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.MlDsa

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev mScrLen (p : Params) : Nat := messageScratchWords p * 8

theorem mScr_eq (p : Params) : mScrLen p = oE p + 1024 := by
  simp only [mScrLen, messageScratchWords, oE]; omega_using []

theorem skLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.skLen ∧ p.skLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

theorem pkLen_ge {p : Params} (hp : p ∈ params) : 128 ≤ p.pkLen ∧ p.pkLen < 2 ^ 16 := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

/-! ## The key -/

/-- The key a function on messages takes, at argument 0: `len` bytes, and
what its contract requires of them. -/
structure KeyArg where
  len : Nat
  pre : Mem → Addr → Prop

/-- An encoded key of `len` bytes, of which the contract requires nothing. -/
abbrev plainKey (len : Nat) : KeyArg := ⟨len, fun _ _ => True⟩

/-- A key that begins with an encoded key of `enc` bytes, and whose
precondition only its own bytes decide. -/
structure KeyArg.Ok (K : KeyArg) (enc : Nat) : Prop where
  ge : 128 ≤ enc
  le : enc ≤ K.len
  lt : K.len < 2 ^ 16
  congr : ∀ {m m' : Mem} {a : Addr}, Spec.Sha3.bytesAt m' a K.len = Spec.Sha3.bytesAt m a K.len →
    K.pre m a → K.pre m' a

theorem plainKey_ok {enc : Nat} (h : 128 ≤ enc ∧ enc < 2 ^ 16) : (plainKey enc).Ok enc :=
  ⟨h.1, Nat.le_refl _, h.2, fun _ h => h⟩

/-! ## The contracts, for a key -/

/-- `signSig`, with a key of `kl` bytes. -/
def signKSig (p : Params) (kl : Nat) : Sig where
  params := [("sk", .array false .u8 kl), ("mu", .array false .u8 64),
    ("rnd", .array false .u8 32), ("sig", .array true .u8 p.sigLen),
    ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `signContract`, with the key `K`. -/
def signKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signKSig p K.len).contract A
    (pre := fun sk _mu _rnd _sig _scratch m => K.pre m sk)
    (post := fun sk mu rnd sig _scratch m m' r =>
      Outcome (fun b => signMu p b (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m rnd 32)) r (Spec.Sha3.bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk mu rnd _sig _scratch m =>
      signLeak p (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m mu 64) (Spec.Sha3.bytesAt m rnd 32))

theorem signContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signContract p A stack = signKContract p (plainKey p.skLen) A stack := rfl

/-- `verifySig`, with a key of `kl` bytes. -/
def verifyKSig (p : Params) (kl : Nat) : Sig where
  params := [("pk", .array false .u8 kl), ("mu", .array false .u8 64),
    ("sig", .array false .u8 p.sigLen), ("scratch", .array true .u64 (scratchWords p))]
  ret := some .u32

/-- `verifyContract`, with the key `K`. -/
def verifyKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (verifyKSig p K.len).contract A
    (pre := fun pk _mu _sig _scratch m => K.pre m pk)
    (post := fun pk mu sig _scratch m _m' r =>
      let v := fun b => verifyMu p b (Spec.Sha3.bytesAt m pk p.pkLen) (Spec.Sha3.bytesAt m mu 64)
        (Spec.Sha3.bytesAt m sig p.sigLen)
      (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk mu sig _scratch m =>
      leakBytes (Spec.Sha3.bytesAt m pk p.pkLen ++ Spec.Sha3.bytesAt m mu 64 ++ Spec.Sha3.bytesAt m sig p.sigLen))

theorem verifyContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    verifyContract p A stack = verifyKContract p (plainKey p.pkLen) A stack := rfl

/-- `signMessageSig`, with a key of `kl` bytes. -/
def signMessageKSig (p : Params) (kl : Nat) : Sig where
  params := [("sk", .array false .u8 kl), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("rnd", .array false .u8 32),
    ("sig", .array true .u8 p.sigLen), ("scratch", .array true .u64 (messageScratchWords p))]
  ret := some .u32

/-- `signMessageContract`, with the key `K`. -/
def signMessageKContract (p : Params) (K : KeyArg) {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  (signMessageKSig p K.len).contract A
    (pre := fun sk _msg _msgLen _ctx _ctxLen _rnd _sig _scratch m => K.pre m sk)
    (post := fun sk msg msgLen ctx ctxLen rnd sig _scratch m m' r =>
      match formatMessage (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        Outcome (fun b => signInternal p b (Spec.Sha3.bytesAt m sk p.skLen) M' (Spec.Sha3.bytesAt m rnd 32)) r
          (Spec.Sha3.bytesAt m' sig p.sigLen))
    (writeArgs := true) (stack := stack)
    (leak := some fun sk msg msgLen ctx ctxLen rnd _sig _scratch m =>
      signMessageLeak p (Spec.Sha3.bytesAt m sk p.skLen) (Spec.Sha3.bytesAt m msg msgLen.toNat)
        (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m rnd 32))

theorem signMessageContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    signMessageContract p A stack = signMessageKContract p (plainKey p.skLen) A stack := rfl

/-- `verifyMessageCachedSig`, with a key of `kl` bytes. -/
def verifyMessageKSig (p : Params) (kl : Nat) : Sig where
  params := [("pk", .array false .u8 kl), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .array false .u8 p.sigLen),
    ("scratch", .array true .u64 (messageScratchWords p)), ("tr", .array false .u8 64)]
  ret := some .u32

/-- `verifyMessageCachedContract`, with a key of `kl` bytes, of which and of
`tr` it requires `VP`. -/
def verifyMessageKContract (p : Params) (kl : Nat) (VP : Mem → Addr → Addr → Prop) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (verifyMessageKSig p kl).contract A
    (pre := fun pk _msg _msgLen _ctx _ctxLen _sig _scratch tr m => VP m pk tr)
    (post := fun pk msg msgLen ctx ctxLen sig _scratch _tr m _m' r =>
      match formatMessage (Spec.Sha3.bytesAt m ctx ctxLen.toNat) (Spec.Sha3.bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        let v := fun b => verifyInternal p b (Spec.Sha3.bytesAt m pk p.pkLen) M' (Spec.Sha3.bytesAt m sig p.sigLen)
        (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true) (stack := stack)
    (leak := some fun pk msg msgLen ctx ctxLen sig _scratch _tr m =>
      leakBytes (Spec.Sha3.bytesAt m pk p.pkLen ++ Spec.Sha3.bytesAt m msg msgLen.toNat ++
        Spec.Sha3.bytesAt m ctx ctxLen.toNat ++ Spec.Sha3.bytesAt m sig p.sigLen))

/-- What `verifyMessageCachedContract` requires of `pk` and `tr`. -/
abbrev plainTr (p : Params) (m : Mem) (pk tr : Addr) : Prop :=
  Spec.Sha3.bytesAt m tr 64 = pkTr (Spec.Sha3.bytesAt m pk p.pkLen)

theorem verifyMessageCachedContract_eq (p : Params) {M : ISA} (A : Abi M) (stack : Nat) :
    verifyMessageCachedContract p A stack = verifyMessageKContract p p.pkLen (plainTr p) A stack := rfl

section
variable (s : State)

/-- Argument `i`, a pointer to `n` bytes. -/
abbrev aR (i n : Nat) : Region := ⟨(arg s i).setWidth 64, n⟩
abbrev msgRg : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
abbrev ctxRg : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
/-- The `n` bytes of arguments. -/
abbrev sArgs (n : Nat) : Region := ⟨argAddr s 0, n⟩
/-- The return address. -/
abbrev sRet : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
/-- The `n` bytes of stack the contract gives. -/
abbrev sStk (n : Nat) : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 n, n⟩

end

theorem stk_eq {s : State} {n : Nat} (h : n ≤ (s.gpr .esp).toNat) : sStk s n = below (s.gpr .esp) n := by
  simp only [sStk, below]; rw [Taint.sub_setWidth h]

/-! ## Signing -/

/-- The precondition of `signMessageKContract p K X86.abi 176`. -/
structure SPre (p : Params) (K : KeyArg) (s : State) : Prop where
  sp : 176 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 32 ≤ 2 ^ 32
  rd : s.rd = [aR s 0 K.len, msgRg s, ctxRg s, aR s 5 32]
  wr : s.wr = [aR s 6 p.sigLen, aR s 7 (mScrLen p), sArgs s 32]
  skSig : (aR s 0 K.len).Disjoint (aR s 6 p.sigLen)
  skScr : (aR s 0 K.len).Disjoint (aR s 7 (mScrLen p))
  skArgs : (aR s 0 K.len).Disjoint (sArgs s 32)
  msgSig : (msgRg s).Disjoint (aR s 6 p.sigLen)
  msgScr : (msgRg s).Disjoint (aR s 7 (mScrLen p))
  msgArgs : (msgRg s).Disjoint (sArgs s 32)
  ctxSig : (ctxRg s).Disjoint (aR s 6 p.sigLen)
  ctxScr : (ctxRg s).Disjoint (aR s 7 (mScrLen p))
  ctxArgs : (ctxRg s).Disjoint (sArgs s 32)
  rndSig : (aR s 5 32).Disjoint (aR s 6 p.sigLen)
  rndScr : (aR s 5 32).Disjoint (aR s 7 (mScrLen p))
  rndArgs : (aR s 5 32).Disjoint (sArgs s 32)
  sigScr : (aR s 6 p.sigLen).Disjoint (aR s 7 (mScrLen p))
  sigArgs : (aR s 6 p.sigLen).Disjoint (sArgs s 32)
  scrArgs : (aR s 7 (mScrLen p)).Disjoint (sArgs s 32)
  rSk : (sRet s).Disjoint (aR s 0 K.len)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rRnd : (sRet s).Disjoint (aR s 5 32)
  rSig : (sRet s).Disjoint (aR s 6 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 7 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s 32)
  kSk : (sStk s 176).Disjoint (aR s 0 K.len)
  kMsg : (sStk s 176).Disjoint (msgRg s)
  kCtx : (sStk s 176).Disjoint (ctxRg s)
  kRnd : (sStk s 176).Disjoint (aR s 5 32)
  kSig : (sStk s 176).Disjoint (aR s 6 p.sigLen)
  kScr : (sStk s 176).Disjoint (aR s 7 (mScrLen p))
  kArgs : (sStk s 176).Disjoint (sArgs s 32)
  nSk : (arg s 0).toNat + K.len ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nRnd : (arg s 5).toNat + 32 ≤ 2 ^ 32
  nSig : (arg s 6).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 7).toNat + mScrLen p ≤ 2 ^ 32
  kp : K.pre s.mem ((arg s 0).setWidth 64)

theorem sPre_of {p : Params} {K : KeyArg} {s : State} (h : (signMessageKContract p K X86.abi 176).pre s) : SPre p K s := by
  sig_pre [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40⟩

/-- The layout of a run of `sign_message` from `s`. -/
def slay (p : Params) (K : KeyArg) (s : State) : Lay where
  SP := s.gpr .esp
  N := 176
  nA := 8
  key := arg s 0
  keyLen := K.len
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 6
  scr := arg s 7
  scrLen := mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6, arg s 7]
  rd := s.rd
  wr := s.wr

theorem slay_ok {p : Params} {K : KeyArg} (hK : K.Ok p.skLen) {s : State} (h : SPre p K s) (h8 : (arg s 4).toNat < 256) :
    (slay p K s).Ok := by
  have hk := stk_eq (s := s) (n := 176) h.sp
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], ⟨show 128 ≤ K.len by have := hK.ge; have := hK.le; omega_arith, hK.lt⟩, by show 56 ≤ 176; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * 8 ≤ _; have := h.spA; omega_using [this], h.nScr, by simp [slay, h.wr], by simp [slay, h.rd],
    by simp [slay, h.rd], by simp [slay, h.rd], h.skScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
    rfl, by show 8 ≤ 8; decide, by show 5 ≤ 8; decide, rfl, rfl, rfl, rfl, rfl, h.nSk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 176).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kSk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

/-! ## Verification -/

/-- Most of the precondition of `verifyMessageKContract p K.len VP X86.abi 172`
(`n = 8`, `T` the cached `tr`): `n` arguments, and the read-only regions
`T s` after the others. -/
structure VPre (p : Params) (K : KeyArg) (n : Nat) (T : State → List Region) (s : State) : Prop where
  sp : 172 ≤ (s.gpr .esp).toNat
  spA : (s.gpr .esp).toNat + 4 + 4 * n ≤ 2 ^ 32
  rd : s.rd = [aR s 0 K.len, msgRg s, ctxRg s, aR s 5 p.sigLen] ++ T s
  wr : s.wr = [aR s 6 (mScrLen p), sArgs s (4 * n)]
  pkScr : (aR s 0 K.len).Disjoint (aR s 6 (mScrLen p))
  pkArgs : (aR s 0 K.len).Disjoint (sArgs s (4 * n))
  msgScr : (msgRg s).Disjoint (aR s 6 (mScrLen p))
  msgArgs : (msgRg s).Disjoint (sArgs s (4 * n))
  ctxScr : (ctxRg s).Disjoint (aR s 6 (mScrLen p))
  ctxArgs : (ctxRg s).Disjoint (sArgs s (4 * n))
  sigScr : (aR s 5 p.sigLen).Disjoint (aR s 6 (mScrLen p))
  sigArgs : (aR s 5 p.sigLen).Disjoint (sArgs s (4 * n))
  scrArgs : (aR s 6 (mScrLen p)).Disjoint (sArgs s (4 * n))
  rPk : (sRet s).Disjoint (aR s 0 K.len)
  rMsg : (sRet s).Disjoint (msgRg s)
  rCtx : (sRet s).Disjoint (ctxRg s)
  rSig : (sRet s).Disjoint (aR s 5 p.sigLen)
  rScr : (sRet s).Disjoint (aR s 6 (mScrLen p))
  rArgs : (sRet s).Disjoint (sArgs s (4 * n))
  kPk : (sStk s 172).Disjoint (aR s 0 K.len)
  kMsg : (sStk s 172).Disjoint (msgRg s)
  kCtx : (sStk s 172).Disjoint (ctxRg s)
  kSig : (sStk s 172).Disjoint (aR s 5 p.sigLen)
  kScr : (sStk s 172).Disjoint (aR s 6 (mScrLen p))
  kArgs : (sStk s 172).Disjoint (sArgs s (4 * n))
  nPk : (arg s 0).toNat + K.len ≤ 2 ^ 32
  nMsg : (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32
  nCtx : (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32
  nSig : (arg s 5).toNat + p.sigLen ≤ 2 ^ 32
  nScr : (arg s 6).toNat + mScrLen p ≤ 2 ^ 32
  hn : n = 7 ∨ n = 8
  kp : K.pre s.mem ((arg s 0).setWidth 64)

/-- The cached `tr`. -/
abbrev trRg (s : State) : List Region := [aR s 7 64]

/-- The precondition of `verifyMessageKContract p K.len VP X86.abi 172`, for a `VP` that gives `K.pre` and
`tr = H(pk, 64)` (`cPre_of`). -/
structure CPre (p : Params) (K : KeyArg) (s : State) : Prop extends VPre p K 8 trRg s where
  scrTr : (aR s 6 (mScrLen p)).Disjoint (aR s 7 64)
  trArgs : (aR s 7 64).Disjoint (sArgs s 32)
  rTr : (sRet s).Disjoint (aR s 7 64)
  kTr : (sStk s 172).Disjoint (aR s 7 64)
  nTr : (arg s 7).toNat + 64 ≤ 2 ^ 32
  tr : Spec.Sha3.bytesAt s.mem ((arg s 7).setWidth 64) 64 =
    pkTr (Spec.Sha3.bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen)

theorem cPre_of {p : Params} {K : KeyArg} {VP : Mem → Addr → Addr → Prop}
    (hV : ∀ {m pk tr}, VP m pk tr → K.pre m pk ∧ Spec.Sha3.bytesAt m tr 64 = pkTr (Spec.Sha3.bytesAt m pk p.pkLen))
    {s : State} (h : (verifyMessageKContract p K.len VP X86.abi 172).pre s) : CPre p K s := by
  sig_pre [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14, a16, a17, a18, a19, a20, a22, a23, a24, a25,
    a26, a27, a29, a30, a31, a32, a33, a34, .inr rfl, (hV a36).1⟩, a13, a15, a21, a28, a35, (hV a36).2⟩

/-- The layout of a run of `verify_message_cached` (`n = 8`) from `s` (`sig`
in the place of `rnd` too). -/
def vlay (p : Params) (K : KeyArg) (n : Nat) (s : State) : Lay where
  SP := s.gpr .esp
  N := 172
  nA := n
  key := arg s 0
  keyLen := K.len
  msg := arg s 1
  len := arg s 2
  ctx := arg s 3
  ctxLen := arg s 4
  rnd := arg s 5
  sig := arg s 5
  scr := arg s 6
  scrLen := mScrLen p
  E := oE p
  argv := [arg s 0, arg s 1, arg s 2, arg s 3, arg s 4, arg s 5, arg s 6] ++
    (List.range (n - 7)).map fun i => arg s (7 + i)
  rd := s.rd
  wr := s.wr

theorem vlay_ok {p : Params} {K : KeyArg} (hK : K.Ok p.pkLen) {n : Nat} {T : State → List Region} {s : State}
    (h : VPre p K n T s) (h8 : (arg s 4).toNat < 256) : (vlay p K n s).Ok := by
  have hk := stk_eq (s := s) (n := 172) h.sp
  have hn := h.hn
  refine ⟨h8, by show oE p + 1024 ≤ mScrLen p; rw [mScr_eq], ⟨show 128 ≤ K.len by have := hK.ge; have := hK.le; omega_arith, hK.lt⟩, by show 56 ≤ 172; decide, h.sp,
    by show (s.gpr .esp).toNat + 4 + 4 * n ≤ _; have := h.spA; omega_using [this], h.nScr, by simp [vlay, h.wr], by simp [vlay, h.rd],
    by simp [vlay, h.rd], by simp [vlay, h.rd], h.pkScr.symm, h.msgScr.symm, h.ctxScr.symm, ?_, ?_,
    h.scrArgs.symm, by show _ ∈ s.wr; rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _),
    by simp only [vlay, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range]; omega_using [hn],
    by show n ≤ 8; omega_using [hn], by show 5 ≤ n; omega_using [hn], rfl, rfl, rfl, rfl, rfl, h.nPk, h.nMsg, h.nCtx⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show (below (s.gpr .esp) 172).Disjoint r
    rw [← hk]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [h.kScr, h.kPk, h.kMsg, h.kCtx, h.kArgs]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.rScr, h.rArgs]

end VG.Proof.MlDsa.X86.Message

end

end


/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message_cached`: the layouts' shapes

Untrusted: everything here is checked by Lean. The contracts' public data,
spelled out (`SPub`, `VPub`), and the layouts of `sign_message` and
`verify_message_cached` (`slay`, `vlay`) meet what the
proofs of the check, the entry and the hashes need (`sShape`, `vShape`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (E0 P0)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- The public data of `signMessageKContract p K X86.abi 176`. -/
structure SPub (p : Params) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : signMessageLeak p (bytesAt s.mem ((arg s 0).setWidth 64) p.skLen)
      (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
      (bytesAt s.mem ((arg s 5).setWidth 64) 32) =
    signMessageLeak p (bytesAt s'.mem ((arg s' 0).setWidth 64) p.skLen)
      (bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat)
      (bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat) (bytesAt s'.mem ((arg s' 5).setWidth 64) 32)
  args : ∀ i < 8, arg s i = arg s' i

theorem spub_of {p : Params} {K : KeyArg} {s s' : State} (h : (signMessageKContract p K X86.abi 176).pub s s') :
    SPub p s s' := by
  sig_pub [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The public data of `verifyMessageKContract p kl VP X86.abi 172` (`n = 8`,
`cpub_of`). -/
structure VPub (p : Params) (n : Nat) (s s' : State) : Prop where
  esp : s.gpr .esp = s'.gpr .esp
  leak : leakBytes (bytesAt s.mem ((arg s 0).setWidth 64) p.pkLen ++
      bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat ++
      bytesAt s.mem ((arg s 5).setWidth 64) p.sigLen) =
    leakBytes (bytesAt s'.mem ((arg s' 0).setWidth 64) p.pkLen ++
      bytesAt s'.mem ((arg s' 1).setWidth 64) (arg s' 2).toNat ++
      bytesAt s'.mem ((arg s' 3).setWidth 64) (arg s' 4).toNat ++ bytesAt s'.mem ((arg s' 5).setWidth 64) p.sigLen)
  args : ∀ i < n, arg s i = arg s' i

theorem cpub_of {p : Params} {kl : Nat} {VP : Mem → Addr → Addr → Prop} {s s' : State}
    (h : (verifyMessageKContract p kl VP X86.abi 172).pub s s') : VPub p 8 s s' := by
  sig_pub [verifyMessageKContract, verifyMessageKSig, X86.abi, X86.argSlots, X86.argVal,
    X86.argBytes] at h
  obtain ⟨e₁, e₂, a0, a1, a2, a3, a4, a5, a6, a7⟩ := h
  refine ⟨e₁, e₂, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7

/-- The leaf's frame, below the stack pointer on entry. -/
theorem frame_eq {s : State} (h : 16 ≤ (s.gpr .esp).toNat) :
    (⟨(E0 s).setWidth 64 - 16#64, 16⟩ : Region) = below (s.gpr .esp) 16 := by
  simp only [below]; rw [Taint.sub_setWidth h]

theorem sShape {p : Params} {K : KeyArg} (hK : K.Ok p.skLen) : Shape (SPre p K) (SPub p) (slay p K) 7 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ _ i hi := by
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ _ := by show 7 < 8; decide
  E _ _ := rfl
  ok _ h₀ h8 := slay_ok hK h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega_using [this],
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega_using [this]⟩
  fit _ h₀ := by show _ + 4 + 4 * 8 ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega_using [this])]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega_using []) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  n5 _ _ := by show 5 ≤ 8; decide
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ _ _ hq := ⟨hq.args 4 (by decide), hq.args 7 (by decide)⟩
  pubL _ _ _ _ hq := ⟨hq.esp, by simp only [slay, hq.args 0 (by decide), hq.args 1 (by decide),
      hq.args 2 (by decide), hq.args 3 (by decide), hq.args 4 (by decide), hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)], by simp only [Lay.X32, slay, hq.args 7 (by decide)], rfl,
    hq.args 0 (by decide), hq.args 1 (by decide), hq.args 2 (by decide), hq.args 3 (by decide),
    hq.args 4 (by decide)⟩

theorem vlay_argv {p : Params} {K : KeyArg} {n : Nat} (hn : n = 7 ∨ n = 8) (s : State) :
    ∀ i < n, (vlay p K n s).argv.getD i 0 = arg s i := by
  rcases hn with rfl | rfl <;> intro i hi
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl

theorem vShape {p : Params} {K : KeyArg} (hK : K.Ok p.pkLen) {n : Nat} {T : State → List Region} :
    Shape (VPre p K n T) (VPub p n) (vlay p K n) 6 p where
  sp _ _ := rfl
  rd _ _ := rfl
  wr _ _ := rfl
  argv s₀ h₀ := vlay_argv h₀.hn s₀
  ctxLen _ _ := rfl
  scr _ _ := rfl
  siLt _ h₀ := by show 6 < n; have := h₀.hn; omega_using [this]
  E _ _ := rfl
  ok _ h₀ h8 := vlay_ok hK h₀ h8
  e16 s₀ h₀ := ⟨by show 16 ≤ (s₀.gpr .esp).toNat; have := h₀.sp; omega_using [this],
    by show (s₀.gpr .esp).toNat + 4 ≤ _; have := h₀.spA; omega_using [this]⟩
  fit _ h₀ := by show _ + 4 + 4 * n ≤ _; have := h₀.spA; omega
  fd s₀ h₀ := by
    rw [frame_eq (by have := h₀.sp; omega_using [this])]
    exact (stk_eq h₀.sp ▸ h₀.kArgs).sub_left (below_sub (by omega_using []) h₀.sp)
  ain _ h₀ := List.mem_append_right _ (by
    rw [h₀.wr]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  n5 _ h₀ := by show 5 ≤ n; have := h₀.hn; omega_using [this]
  pubE _ _ _ _ hq := hq.esp
  pubA _ _ h₀ _ hq := ⟨hq.args 4 (by have := h₀.hn; omega_using [this]), hq.args 6 (by have := h₀.hn; omega_using [this])⟩
  pubL s₀ s₀' h₀ _ hq := by
    have hn := h₀.hn
    have e : ((List.range (n - 7)).map fun i => arg s₀ (7 + i)) = (List.range (n - 7)).map fun i => arg s₀' (7 + i) :=
      List.map_congr_left fun i hi => hq.args _ (by rw [List.mem_range] at hi; omega_using [hi])
    exact ⟨hq.esp, by simp only [vlay, hq.args 0 (by omega_using [hn]), hq.args 1 (by omega_using [hn]),
      hq.args 2 (by omega_using [hn]), hq.args 3 (by omega_using [hn]), hq.args 4 (by omega_using [hn]), hq.args 5 (by omega_using [hn]),
      hq.args 6 (by omega_using [hn]), e], by simp only [Lay.X32, vlay, hq.args 6 (by omega_using [hn])], rfl,
    hq.args 0 (by omega_using [hn]), hq.args 1 (by omega_using [hn]), hq.args 2 (by omega_using [hn]), hq.args 3 (by omega_using [hn]),
    hq.args 4 (by omega_using [hn])⟩

/-- A shape, for a stronger precondition. -/
theorem Shape.pre_mono {Pre Pre' : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {si : Nat}
    {p : Params} (hS : Shape Pre Pub lay si p) (h : ∀ s, Pre' s → Pre s) : Shape Pre' Pub lay si p where
  sp s₀ h₀ := hS.sp s₀ (h _ h₀)
  rd s₀ h₀ := hS.rd s₀ (h _ h₀)
  wr s₀ h₀ := hS.wr s₀ (h _ h₀)
  argv s₀ h₀ := hS.argv s₀ (h _ h₀)
  ctxLen s₀ h₀ := hS.ctxLen s₀ (h _ h₀)
  scr s₀ h₀ := hS.scr s₀ (h _ h₀)
  siLt s₀ h₀ := hS.siLt s₀ (h _ h₀)
  E s₀ h₀ := hS.E s₀ (h _ h₀)
  ok s₀ h₀ := hS.ok s₀ (h _ h₀)
  e16 s₀ h₀ := hS.e16 s₀ (h _ h₀)
  fit s₀ h₀ := hS.fit s₀ (h _ h₀)
  fd s₀ h₀ := hS.fd s₀ (h _ h₀)
  ain s₀ h₀ := hS.ain s₀ (h _ h₀)
  n5 s₀ h₀ := hS.n5 s₀ (h _ h₀)
  pubE s₀ s₀' h₀ h₀' := hS.pubE s₀ s₀' (h _ h₀) (h _ h₀')
  pubA s₀ s₀' h₀ h₀' := hS.pubA s₀ s₀' (h _ h₀) (h _ h₀')
  pubL s₀ s₀' h₀ h₀' := hS.pubL s₀ s₀' (h _ h₀) (h _ h₀')

end VG.Proof.MlDsa.X86.Message

end

end

/-!
# ML-DSA on x86 (32-bit), `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. With `μ` at `X + 840`, the
call of `vg_mldsa*_sign(sk, μ, rnd, sig, scratch)`, or of
`vg_mldsa*_sign_prepared` (`signCall_piece`): its arguments in `eax`, `ecx`,
`edx`, `ebx` and `edi`, pushed; its precondition (`signKContract p K X86.abi
176`), from `sign_message`'s; what it leaks, which is what `sign_message`
may (`leak_eq`); and its result, which is `sign_message`'s.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Only Piece P0 E0 frameR retR LeafEnd)
open VG.Proof.MlKem.X86.Top (entry_regions entry_self covers_of)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

/-- A signing function on `μ`, as `sign_message` calls it. -/
structure SignFn (p : Params) (K : KeyArg) (c : Prog isa) : Prop where
  ver : Verified X86.target c (signKContract p K X86.abi 136)
  nosp : NoSp c
  su : stackUse c ≤ 136

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) :=
  [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6), (.edi, .arg 7)]

section
variable (p : Params) (K : KeyArg) (s₀ : State)

/-- The message representative of the run from `s₀`. -/
abbrev sMu : List Byte :=
  H (bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64 ++ hdrBytes (slay p K s₀) ++
    bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++ bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
    64

/-- The regions the signing function on `μ` is given. -/
abbrev sRd : List Region :=
  [⟨(arg s₀ 0).setWidth 64, K.len⟩, ⟨((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩,
    ⟨(arg s₀ 5).setWidth 64, 32⟩]
abbrev sWr : List Region :=
  [⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, ⟨(arg s₀ 7).setWidth 64, sScr p⟩, below (slay p K s₀).E1 20]

/-- What `sign_message` changes: `scratch`, the stack, and `sig`. -/
abbrev sW : List Region := [(slay p K s₀).SC, (slay p K s₀).STK, ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩]

/-- The result. -/
def SB (s : State) : Prop :=
  (arg s₀ 4).toNat < 256 ∧
    Outcome (fun b => signMu p b (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (sMu p K s₀)
      (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32)) (s.gpr .eax) (bytesAt s.mem ((arg s₀ 6).setWidth 64) p.sigLen)

end

section
variable {p : Params} {K : KeyArg}

/-- What `sign_message` leaks is what the signing function on `μ` leaks, for
the `μ` it computes. -/
theorem leak_eq {s₀ : State} (h₀ : SPre p K s₀) (h8 : (arg s₀ 4).toNat < 256) (hK : K.Ok p.skLen) :
    signMessageLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen)
        (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat)
        (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat) (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) =
      signLeak p (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen) (sMu p K s₀)
        (bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32) := by
  have := h₀.nSk
  have := hK.le
  have := hK.ge
  rw [signMessageLeak, formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega_arith)]
  simp only [sMu, hdrBytes, slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega_arith)]


/-- The values of the arguments. -/
theorem signArgs_val {s₀ s s₁ : State} (hc : CtxO (slay p K) s₀ s) (hs : SetPost signArgs s s₁) :
    s₁.gpr .eax = arg s₀ 0 ∧ s₁.gpr .ecx = (slay p K s₀).X32 + BitVec.ofNat 32 840 ∧ s₁.gpr .edx = arg s₀ 5 ∧
      s₁.gpr .ebx = arg s₀ 6 ∧ s₁.gpr .edi = arg s₀ 7 := by
  have h8 : ∀ {i}, i < 8 → i < (slay p K s₀).nA := fun h => h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs.1 (.eax, .arg 0) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ecx, .off oMU) (by simp), hc.ctx.off]; rfl
  · rw [hs.1 (.edx, .arg 5) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.ebx, .arg 6) (by simp), hc.ctx.argV (h8 (by decide))]; rfl
  · rw [hs.1 (.edi, .arg 7) (by simp), hc.ctx.argV (h8 (by decide))]; rfl

theorem signArgs_ok : argsOk 8 signArgs = true := by decide

/-- The facts about regions the call needs. -/
structure SRegs (p : Params) (K : KeyArg) (s₀ : State) : Prop where
  hE : 160 ≤ (slay p K s₀).E1.toNat
  scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, sScr p⟩ (slay p K s₀).SC
  argsSub : Region.Sub (below (slay p K s₀).E1 20) (slay p K s₀).STK
  muSub : Region.Sub ⟨((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (slay p K s₀).SC
  kSk : (slay p K s₀).STK.Disjoint ⟨(arg s₀ 0).setWidth 64, K.len⟩
  kMu : (slay p K s₀).STK.Disjoint ⟨((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩
  kRnd : (slay p K s₀).STK.Disjoint ⟨(arg s₀ 5).setWidth 64, 32⟩
  kSig : (slay p K s₀).STK.Disjoint ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩
  kScr : (slay p K s₀).STK.Disjoint ⟨(arg s₀ 7).setWidth 64, sScr p⟩
  muScr : Region.Disjoint ⟨((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ ⟨(arg s₀ 7).setWidth 64, sScr p⟩

theorem sregs {s₀ : State} (h₀ : SPre p K s₀) (hL : (slay p K s₀).Ok) : SRegs p K s₀ := by
  have hsp := h₀.sp
  have hE : 160 ≤ (slay p K s₀).E1.toNat := by
    show 160 ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega_arith)]; omega_arith
  have hk : ∀ {R : Region}, (sStk s₀ 176).Disjoint R → (slay p K s₀).STK.Disjoint R := fun h =>
    (stk_eq hsp ▸ h).sub_left hL.stk_sub
  have scrSub : Region.Sub ⟨(arg s₀ 7).setWidth 64, sScr p⟩ (slay p K s₀).SC :=
    (within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega_arith)).sub
  have muSub : Region.Sub ⟨((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64, 64⟩ (slay p K s₀).SC := by
    rw [mu_eq hL]; exact hL.sub_sc (e := 840) (k := 64) (by omega_arith)
  refine ⟨hE, scrSub, below_sub (by show 20 ≤ 176 - 16; decide) (by show 176 - 16 ≤ _; omega_arith), muSub, hk h₀.kSk, by rw [mu_eq hL]; exact k_mu hL, hk h₀.kRnd,
    hk h₀.kSig, hL.kSC.sub_right scrSub, ?_⟩
  have hx := hL.x_eq
  have := h₀.nScr
  have := mScr_eq p
  have e : ((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64 =
      (arg s₀ 7).setWidth 64 + BitVec.ofNat 64 (oE p + 840) := by
    rw [mu_eq hL, Lay.MU, hx, add_add]; rfl
  rw [e]
  have d := Offset.disjoint ((arg s₀ 7).setWidth 64) (d := oE p + 840) (n := 64) (e := 0) (k := sScr p)
    (.inr (by simp only [oE, sScr]; omega_arith)) (by omega_arith) (by simp only [oE, sScr] at *; omega_arith)
  rwa [BitVec.add_zero] at d

/-- Bytes apart from the stack and from `scratch` are, on the callee's entry, as on `sign_message`'s. -/
theorem sign_bytes {s₀ s s₁ : State} (h₀ : SPre p K s₀) (hc : CtxO (slay p K) s₀ s) (hs : SetPost signArgs s s₁)
    {R : Region} (hk : (sStk s₀ 176).Disjoint R) (hx : (slay p K s₀).SC.Disjoint R) (hn : R.len ≤ 2 ^ 64) :
    bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hL := hc.ok
  have hc1 := SetPost.ctx signArgs_ok hs hc.ctx
  have hE := (sregs h₀ hL).hE
  have hsp1 : s₁.gpr .esp = (slay p K s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ Proof.MlKem.X86.rs5)
  rw [hsp1] at fr
  have b24 : Region.Sub (below (slay p K s₀).E1 (4 * Proof.MlKem.X86.rs5.length + 4)) (slay p K s₀).STK :=
    below_sub (by show 24 ≤ 176 - 16; decide) (by show 176 - 16 ≤ _; omega_arith)
  have hsp := h₀.sp
  have hkS : (slay p K s₀).STK.Disjoint R := (stk_eq hsp ▸ hk).sub_left hL.stk_sub
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega_arith)
  rw [Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hkS.sub_left b24).symm) hn hi,
    hs.2.mem, hc.ctx.bytesAt_eq hx hkS hn]
  exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := R) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((stk_eq hsp ▸ hk).sub_left (below_sub (by decide) hsp)).symm) hn hi

/-- The encoded key, on the callee's entry. -/
theorem sign_bSk {s₀ s s₁ : State} (hK : K.Ok p.skLen) (h₀ : SPre p K s₀) (hc : CtxO (slay p K) s₀ s)
    (hs : SetPost signArgs s s₁) {l : Nat} (hl : l ≤ K.len) :
    bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) l =
      bytesAt s₀.mem ((arg s₀ 0).setWidth 64) l := by
  have w : Region.Sub ⟨(arg s₀ 0).setWidth 64, l⟩ ⟨(arg s₀ 0).setWidth 64, K.len⟩ := (within_base _ hl).sub
  have := hK.lt
  exact sign_bytes (R := ⟨_, l⟩) h₀ hc hs (h₀.kSk.sub_right w) (hc.ok.xKey.sub_right w) (by show l ≤ 2 ^ 64; omega_using [hl, this])

/-- The callee's precondition. -/
theorem sign_callPre {s₀ s s₁ : State} (hK : K.Ok p.skLen) (h₀ : SPre p K s₀) (hc : CtxO (slay p K) s₀ s)
    (hs : SetPost signArgs s s₁) : CallPre (signKContract p K X86.abi 136) Proof.MlKem.X86.rs5 (sRd p K s₀) (sWr p K s₀) s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := signArgs_val hc hs
  have R := sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (slay p K s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v0
  have a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (slay p K s₀).X32 + BitVec.ofNat 32 840 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v1
  have a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v2
  have a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v3
  have a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7 := by
    rw [callEntry_arg fit (by decide) (by decide)]; exact v4
  have eA : argAddr (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = ((slay p K s₀).E1 - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hsp1]; rfl
  have eSp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (slay p K s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4) := by
    rw [callEntry_esp', hsp1]; rfl
  have cv := covers_of (s := s₁) (n := 5) (rd := sRd p K s₀) (wr := sWr p K s₀) (fun r hr => ?_) fun r hr => ?_
  rotate_left
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact withinRW hc1 ⟨_, List.mem_append_left _ hL.inKey, within_self _⟩
    · exact withinRW hc1 (by rw [mu_eq hL]; exact cov_x hL (e := 840) (k := 64) (by omega_arith))
    · exact withinRW hc1 ⟨_, List.mem_append_left _ (by show _ ∈ s₀.rd; rw [h₀.rd]; simp), within_self _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr (withinW hc1 ⟨_, by show _ ∈ s₀.wr; rw [h₀.wr]; simp, within_self _⟩)
    · exact .inr (withinW hc1 ⟨_, hL.inSC, within_base _ (by show sScr p ≤ mScrLen p; simp only [sScr, mScrLen, messageScratchWords]; omega_arith)⟩)
    · exact .inl (by rw [hsp1])
  refine ⟨?_, cv.1, cv.2⟩
  obtain ⟨rSk₁, rSk₂, rSk₃⟩ := entry_regions (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith) R.kSk
  obtain ⟨rMu₁, rMu₂, rMu₃⟩ := entry_regions (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith) R.kMu
  obtain ⟨rRnd₁, rRnd₂, rRnd₃⟩ := entry_regions (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith) R.kRnd
  obtain ⟨rSig₁, rSig₂, rSig₃⟩ := entry_regions (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith) R.kSig
  obtain ⟨rScr₁, rScr₂, rScr₃⟩ := entry_regions (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith) R.kScr
  obtain ⟨rA₂, rA₃⟩ := entry_self (E := (slay p K s₀).E1) (k := 5) (K := 136) (by omega_arith)
  generalize he : (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eA eSp ⊢
  sig_pre [signKContract, signKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  subst he
  simp only [arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp]
  have hX := hL.x32_lt
  refine ⟨by rw [sub_toNat (by omega_arith)]; omega_arith, by rw [sub_toNat (by omega_arith)]; have := (slay p K s₀).E1.isLt; omega_arith,
    trivial, trivial, h₀.skSig, h₀.skScr.sub_right R.scrSub, rSk₁, h₀.sigScr.symm.sub_left R.muSub, R.muScr, rMu₁,
    h₀.rndSig, h₀.rndScr.sub_right R.scrSub, rRnd₁, h₀.sigScr.sub_right R.scrSub, rSig₁, rScr₁,
    rSk₂, rMu₂, rRnd₂, rSig₂, rScr₂, rA₂, rSk₃, rMu₃, rRnd₃, rSig₃, rScr₃, rA₃, h₀.nSk,
    by rw [hL.x32_toNat (by omega_arith)]; omega_arith, h₀.nRnd, h₀.nSig,
    by have := h₀.nScr; simp only [mScrLen, messageScratchWords] at this ⊢; omega_arith,
    hK.congr (sign_bSk hK h₀ hc hs (Nat.le_refl _)) h₀.kp⟩

/-- What the signing function on `μ` sees on entry. -/
structure SView (p : Params) (K : KeyArg) (s₀ s₁ : State) : Prop where
  a0 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 0 = arg s₀ 0
  a1 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 1 = (slay p K s₀).X32 + BitVec.ofNat 32 840
  a2 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 2 = arg s₀ 5
  a3 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 3 = arg s₀ 6
  a4 : arg (pushed Proof.MlKem.X86.rs5 s₁).callEntry 4 = arg s₀ 7
  esp : (pushed Proof.MlKem.X86.rs5 s₁).callEntry.gpr .esp = (slay p K s₀).E1 - BitVec.ofNat 32 (4 * 5 + 4)
  bSk : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 0).setWidth 64) p.skLen =
    bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen
  bMu : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem (((slay p K s₀).X32 + BitVec.ofNat 32 840).setWidth 64) 64 =
    sMu p K s₀
  bRnd : bytesAt (pushed Proof.MlKem.X86.rs5 s₁).callEntry.mem ((arg s₀ 5).setWidth 64) 32 =
    bytesAt s₀.mem ((arg s₀ 5).setWidth 64) 32

theorem sign_view {s₀ s s₁ : State} (hK : K.Ok p.skLen) (h₀ : SPre p K s₀) (hc : CtxO (slay p K) s₀ s)
    (hμ : bytesAt s.mem (slay p K s₀).MU 64 = sMu p K s₀) (hs : SetPost signArgs s s₁) : SView p K s₀ s₁ := by
  have hL := hc.ok
  have hc1 := SetPost.ctx signArgs_ok hs hc.ctx
  obtain ⟨v0, v1, v2, v3, v4⟩ := signArgs_val hc hs
  have R := sregs h₀ hL
  have hE := R.hE
  have hsp1 : s₁.gpr .esp = (slay p K s₀).E1 := hc1.esp
  have fit : 4 * Proof.MlKem.X86.rs5.length + 4 ≤ (s₁.gpr .esp).toNat := by
    rw [hsp1]; simp only [List.length_cons, List.length_nil]; omega_arith
  have fr := callEntry_frame fit (by decide : Reg.esp ∉ Proof.MlKem.X86.rs5)
  rw [hsp1] at fr
  have b24 : Region.Sub (below (slay p K s₀).E1 (4 * Proof.MlKem.X86.rs5.length + 4)) (slay p K s₀).STK :=
    below_sub (by show 24 ≤ 176 - 16; decide) (by show 176 - 16 ≤ _; omega_arith)
  refine ⟨by rw [callEntry_arg fit (by decide) (by decide)]; exact v0,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v1,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v2,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v3,
    by rw [callEntry_arg fit (by decide) (by decide)]; exact v4,
    by rw [callEntry_esp', hsp1]; rfl, sign_bSk hK h₀ hc hs hK.le, ?_,
    sign_bytes (R := ⟨_, 32⟩) h₀ hc hs h₀.kRnd h₀.rndScr.symm (by show 32 ≤ 2 ^ 64; decide)⟩
  rw [Proof.MlKem.bytesAt_congr fun _ hi => fr.bytes (R := ⟨_, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (R.kMu.sub_left b24).symm) (by show 64 ≤ 2 ^ 64; decide) hi,
    hs.2.mem, mu_eq hL]
  exact hμ

/-- The call of the signing function on `μ`. -/
theorem signCall_piece (hK : K.Ok p.skLen) {n : String} {f : Prog isa} (hf : SignFn p K f) :
    Piece (SPre p K) (SPub p) (fun s₀ s => CtxO (slay p K) s₀ s ∧ bytesAt s.mem (slay p K s₀).MU 64 = sMu p K s₀)
      (fun s₀ s => LeafEnd s₀ (sW p K s₀) s ∧ SB p K s₀ s)
      (.seq (.block (setArgs signArgs)) (Impl.MlKem.X86.callRet rs5 n f)) := by
  refine argsRet_piece hf.ver.1 hf.ver.2.1 hf.nosp (by decide) (by decide) (by native_taint_decide) (sShape hK).pubL
    (fun _ _ _ h => h.1) (fun _ _ => by show argsOk 8 signArgs = true; decide) (sRd p K) (sWr p K)
    (fun s₀ s₀' h₀ h₀' hq => ?_) (fun s₀ s h₀ ha => ?_) (fun s₀ s s₁ h₀ ha hs => ?_)
    (fun s₀ s₀' s s' s₁ s₁' h₀ h₀' hq ha ha' hs hs' => ?_) (fun s₀ s s₁ s' h₀ ha hs e₁ e₂ e₃ fr post => ?_)
  · refine ⟨?_, ?_⟩
    · simp only [sRd, Lay.X32, slay, hq.args 0 (by decide), hq.args 5 (by decide), hq.args 7 (by decide)]
    · simp only [sWr, Lay.E1, slay, hq.esp, hq.args 6 (by decide), hq.args 7 (by decide)]
  · have := hf.su
    have := h₀.sp
    show _ ≤ (s₀.gpr .esp - BitVec.ofNat 32 16).toNat
    rw [sub_toNat (by omega_arith)]
    simp only [List.length_cons, List.length_nil]
    omega_arith
  · exact sign_callPre hK h₀ ha.1 hs
  · obtain ⟨hc, hμ⟩ := ha
    obtain ⟨hc', hμ'⟩ := ha'
    have hp' := (sShape hK).pubL s₀ s₀' h₀ h₀' hq
    have lk := (leak_eq h₀ hc.ok.ctxLt hK).symm.trans (hq.leak.trans (leak_eq h₀' hc'.ok.ctxLt hK))
    obtain ⟨a0, a1, a2, a3, a4, eS, bSk, bMu, bRnd⟩ := sign_view hK h₀ hc hμ hs
    obtain ⟨a0', a1', a2', a3', a4', eS', bSk', bMu', bRnd'⟩ := sign_view hK h₀' hc' hμ' hs'
    generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 a4 eS bSk bMu bRnd ⊢
    generalize (pushed Proof.MlKem.X86.rs5 s₁').callEntry = e' at a0' a1' a2' a3' a4' eS' bSk' bMu' bRnd' ⊢
    sig_pub [signKContract, signKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [arg_withRegions, a0, a1, a2, a3, a4, a0', a1', a2', a3', a4', eS, eS']
    rw [bSk, bMu, bRnd, bSk', bMu', bRnd']
    exact ⟨by simp only [Lay.E1, hp'.sp], lk, hq.args 0 (by decide), by rw [hp'.x], hq.args 5 (by decide),
      hq.args 6 (by decide), hq.args 7 (by decide)⟩
  · obtain ⟨hc, hμ⟩ := ha
    have hL := hc.ok
    have R := sregs h₀ hL
    have hE := R.hE
    have hsp1 : s₁.gpr .esp = (slay p K s₀).E1 := (SetPost.ctx signArgs_ok hs hc.ctx).esp
    refine ⟨CtxO.leafEnd (sShape hK) h₀ hc (W := sW p K s₀) (by simp) (rs := sWr p K s₀ ++
        [below (s₁.gpr .esp) (4 * Proof.MlKem.X86.rs5.length + stackUse f + 4)]) (by rw [← hs.2.mem]; exact fr)
        (fun r hr => ?_) ((e₃ .esp (by decide)).trans (hs.esp signArgs_ok)) (e₁.trans hs.2.rd)
        (e₂.trans hs.2.wr), ?_⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(arg s₀ 6).setWidth 64, p.sigLen⟩, by simp, fun _ h => h⟩
      · exact ⟨(slay p K s₀).SC, by simp, R.scrSub⟩
      · exact ⟨(slay p K s₀).STK, by simp, R.argsSub⟩
      · refine ⟨(slay p K s₀).STK, by simp, ?_⟩
        rw [hsp1]
        have := hf.su
        exact below_sub (by show _ ≤ 176 - 16; simp only [List.length_cons, List.length_nil]; omega_arith)
          (by show 176 - 16 ≤ _; omega_arith)
    · have v := sign_view hK h₀ hc hμ hs
      obtain ⟨s₂, m₂, g₂, post⟩ := post
      obtain ⟨a0, a1, a2, a3, -, -, bSk, bMu, bRnd⟩ := v
      generalize (pushed Proof.MlKem.X86.rs5 s₁).callEntry = e at a0 a1 a2 a3 bSk bMu bRnd post
      sig_post [signKContract, signKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at post
      simp only [arg_withRegions, a0, a1, a2, a3] at post
      rw [bSk, bMu, bRnd, Proof.MlKem.X86.setWidth_append32, g₂] at post
      obtain kS : bytesAt s'.mem ((arg s₀ 6).setWidth 64) p.sigLen = bytesAt s₂.mem ((arg s₀ 6).setWidth 64) p.sigLen :=
        Proof.MlKem.bytesAt_congr fun i hi => m₂.bytes (R := ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩) (fun r hr => by
          rw [List.mem_singleton] at hr; subst hr; rw [hsp1]; exact (R.kSig.sub_left R.argsSub).symm)
          (by show p.sigLen ≤ 2 ^ 64; have := h₀.nSig; omega_arith) hi
      rw [← kS] at post
      exact ⟨hc.ok.ctxLt, post⟩

end

end VG.Proof.MlDsa.X86.Message

end

end

/-!
# ML-DSA on x86 (32-bit), `sign_message`: correct and constant time

Untrusted: everything here is checked by Lean. The body past the entry:
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)`, for `tr` the 64 bytes of `sk` at
64, then the call of the signing function on it (`signRest_piece`); in the
leaf, after the check (`signMessage_piece`); and what that says of the
contract's postcondition (`signMessage_post`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Piece P0 E0 frameR retR LeafEnd LeafPost)
open VG.Spec.Sha3 (bytesAt)
open VG.Spec.MlDsa

section
variable {p : Params} {K : KeyArg}

/-- Bytes apart from the stack the contract gives, as on entry, after the leaf's push. -/
theorem p0_bytes {s₀ : State} {N : Nat} (hN : 16 ≤ N) (hN' : N ≤ (s₀.gpr .esp).toNat) {a : Addr} {n : Nat}
    (hk : (sStk s₀ N).Disjoint ⟨a, n⟩) (hn : n ≤ 2 ^ 64) :
    bytesAt (P0 s₀).mem a n = bytesAt s₀.mem a n := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by show 16 ≤ _; omega_using [hN, hN'])
  exact Proof.MlKem.bytesAt_congr fun _ hi => hf.bytes (R := ⟨a, n⟩) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ((stk_eq hN' ▸ hk).sub_left (below_sub hN hN')).symm) hn hi

/-- `μ` is the message representative of the formatted message. -/
theorem sMu_eq {s₀ : State} (h₀ : SPre p K s₀) (hK : K.Ok p.skLen) :
    messageRep (skTr (bytesAt s₀.mem ((arg s₀ 0).setWidth 64) p.skLen))
      ([0, BitVec.ofNat 8 (bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat).length] ++
        bytesAt s₀.mem ((arg s₀ 3).setWidth 64) (arg s₀ 4).toNat ++
        bytesAt s₀.mem ((arg s₀ 1).setWidth 64) (arg s₀ 2).toNat) = sMu p K s₀ := by
  have := h₀.nSk
  have := hK.le
  have := hK.ge
  simp only [messageRep, skTr, Proof.MlKem.bytesAt_length]
  rw [Proof.MlKem.bytesAt_slice _ _ (by omega_using [this])]
  simp only [sMu, hdrBytes, slay, List.append_assoc]
  rw [Proof.MlKem.X86.ea_off (by omega_arith)]

/-- `μ`, then the call of the signing function on it. -/
theorem signRest_piece (hK : K.Ok p.skLen) {n : String} {f : Prog isa} (hf : SignFn p K f) :
    Piece (SPre p K) (SPub p) (CtxO (slay p K)) (fun s₀ s => LeafEnd s₀ (sW p K s₀) s ∧ SB p K s₀ s)
      (.seq (muHash (.argOff 0 64)) (.seq (.block (setArgs signArgs)) (Impl.MlKem.X86.callRet rs5 n f))) := by
  have hk := hK.ge
  have hk' := hK.le
  refine Piece.seq ((muHash_piece (lay := slay p K) (.argOff 0 64) (fun s₀ => arg s₀ 0 + BitVec.ofNat 32 64)
    (fun s₀ => bytesAt s₀.mem ((arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64) 64) (by native_taint_decide) (sShape hK).pubL
    (fun _ _ _ h => h) (fun _ _ => by show 5 ≤ 8; decide) (fun _ _ => rfl) rfl
    (fun s₀ s h₀ hc => hc.ctx.argOffV (by show 0 < 8; decide) 64)
    (fun s₀ s₀' h₀ h₀' hq => by rw [hq.args 0 (by decide)])
    (fun s₀ s h₀ hc => ?_) (fun _ _ => Proof.MlKem.bytesAt_length _ _ _) (fun s₀ h₀ hL => ?_)).mono
    (fun _ _ _ h => h) fun s₀ s h₀ ⟨hc, hm⟩ => ⟨hc, ?_⟩) (signCall_piece hK hf)
  · have hL := hc.ok
    have := h₀.nSk
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (slay p K s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega_using [hk, hk', this])]; exact within_off _ (show 64 + 64 ≤ K.len by omega_using [hk, hk'])
    rw [hc.ctx.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide)]
    exact p0_bytes (by decide) h₀.sp (h₀.kSk.sub_right wtr.sub) (by decide)
  · have := h₀.nSk
    have := hK.ge
    have := hK.le
    have wtr : Within ⟨(arg s₀ 0 + BitVec.ofNat 32 64).setWidth 64, 64⟩ (slay p K s₀).KEY := by
      rw [Proof.MlKem.X86.ea_off (by omega_arith)]; exact within_off _ (show 64 + 64 ≤ K.len by omega_using [hk, hk'])
    have hst : Region.Sub ⟨(slay p K s₀).ST, 200⟩ (slay p K s₀).SC := by
      have := hL.sub_sc (e := 0) (k := 200) (by omega_using [])
      simpa only [x0] using this
    refine ⟨?_, ⟨_, List.mem_append_left _ hL.inKey, wtr⟩, (hL.xKey.symm.sub_left wtr.sub).sub_right hst,
      (hL.xKey.symm.sub_left wtr.sub).sub_right (hL.sub_sc (by omega_using [] : 200 + 640 ≤ 1024)),
      hL.kKey.sub_right wtr.sub⟩
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 64) (by decide), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [hm]
    simp only [ctxB, msgB]
    rw [p0_bytes (a := (slay p K s₀).ctx.setWidth 64) (n := (slay p K s₀).ctxLen.toNat) (by decide) h₀.sp h₀.kCtx
        (by have := (arg s₀ 4).isLt; show (arg s₀ 4).toNat ≤ _; omega_using []),
      p0_bytes (a := (slay p K s₀).msg.setWidth 64) (n := (slay p K s₀).len.toNat) (by decide) h₀.sp h₀.kMsg
        (by have := (arg s₀ 2).isLt; show (arg s₀ 2).toNat ≤ _; omega_using [])]
    rfl


/-- What `sign_message` changes is apart from its frame and return address. -/
theorem sign_hW : ∀ s₀, SPre p K s₀ → ∀ r ∈ sW p K s₀, (frameR s₀).Disjoint r ∧ (retR s₀).Disjoint r := by
  intro s₀ h₀ r hr
  have hsp := h₀.sp
  have fr : Region.Sub (frameR s₀) (sStk s₀ 176) := by rw [stk_eq hsp]; exact below_sub (by decide) hsp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨h₀.kScr.sub_left fr, h₀.rScr⟩
  · exact ⟨Proof.MlKem.X86.Top.below_adj (sp := s₀.gpr .esp) (a := 16) (b := 176 - 16) (by omega_using [hsp]),
      (Proof.MlKem.X86.Top.ret_below hsp).sub_right (below_inner (a := 176 - 16) (k := 16) (by omega_using []) hsp)⟩
  · exact ⟨h₀.kSig.sub_left fr, h₀.rSig⟩

theorem nosp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem nosp_ite {cnd : Cond} {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.ite cnd a b) := fun i hi => by
  simp only [VG.instrs, List.mem_append] at hi
  rcases hi with h | h
  exacts [ha i h, hb i h]

theorem enter_nosp (si : Nat) (p : Params) : NoSp (enter si p) := fun i hi => by
  simp only [enter, VG.instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl) | (rfl | rfl | rfl | rfl) <;> rfl

theorem callRet_nosp {rs : List Reg} {n : String} {c : Prog isa} (hc : NoSp c) :
    NoSp (Impl.MlKem.X86.callRet rs n c) := fun i hi => by
  simp only [Impl.MlKem.X86.callRet, VG.instrs, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact hc i hi
  · rfl

/-- The body of a leaf `top (enter si p) rest` never writes `esp`, if `rest` does not. -/
theorem topBody_nosp (si : Nat) (p : Params) {rest : Prog isa} (hr : NoSp rest) :
    NoSp (.seq (.block [.mov .eax (.mem (argAt 4)), .alu .cmp .eax (.imm 256)])
      (.ite .ae (.block [.mov .eax (.imm 2)]) (.seq (enter si p) rest))) :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_ite (NoSp.of_all (by decide +kernel))
    (nosp_seq (enter_nosp si p) hr))

/-- What `sign_message` runs after `enter` never writes `esp`, if the signing
function it calls does not. -/
theorem signRest_nosp {n : String} {f : Prog isa} (hf : NoSp f) :
    NoSp (.seq (muHash (.argOff 0 64))
      (.seq (.block (setArgs [(.eax, .arg 0), (.ecx, .off oMU), (.edx, .arg 5), (.ebx, .arg 6), (.edi, .arg 7)]))
        (Impl.MlKem.X86.callRet rs5 n f))) :=
  nosp_seq (NoSp.of_all (by decide +kernel)) (nosp_seq (NoSp.of_all (by decide +kernel)) (callRet_nosp hf))

/-- `sign_message` never writes `esp`, if the signing function it calls does not. -/
theorem signMessage_nosp (p : Params) {n : String} {f : Prog isa} (hf : NoSp f) : NoSp (signMessage n f p) :=
  KeyGen.NoSp.leaf (topBody_nosp 7 p (signRest_nosp hf))

/-- `sign_message`, in its leaf. -/
theorem signMessage_piece (hK : K.Ok p.skLen) {n : String} {f : Prog isa} (hf : SignFn p K f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true) :
    Piece (SPre p K) (SPub p) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (fun s => (256 ≤ (arg s₀ 4).toNat ∧
      s.gpr .eax = 2) ∨ SB p K s₀ s) s₀ s') (signMessage n f p) :=
  top_piece (sShape hK) tt (sW p K) sign_hW (topBody_nosp 7 p (signRest_nosp hf.nosp)) (signRest_piece hK hf)

theorem signMessage_verified (hK : K.Ok p.skLen) {n : String} {f : Prog isa} (hf : SignFn p K f)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp]) (.block [.mov .esi (.mem (argAt 7)),
      .alu .add .esi (.imm (BitVec.ofNat 32 (oE p)))]) ht).isSome = true)
    (hsat : ∃ s, (signMessageKContract p K X86.abi 176).pre s) :
    Verified X86.target (signMessage n f p) (signMessageKContract p K X86.abi 176) := by
  refine Piece.verified (((signMessage_piece hK hf tt).pre_mono (fun _ h => sPre_of h)
    fun _ _ _ _ h => spub_of h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) hsat
  obtain ⟨habi, -, -, s, hB, hm, hax⟩ := hq
  refine ⟨habi, ?_⟩
  have h₀' := sPre_of h₀
  sig_post [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
  rw [Proof.MlKem.X86.setWidth_append32, hax, Proof.MlKem.bytesAt_congr (Proof.MlKem.X86.leaf_keep
    (r := ⟨(arg s₀ 6).setWidth 64, p.sigLen⟩) hm
    (sign_hW s₀ h₀' _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).1
    (by dsimp only; have := h₀'.nSig; omega_arith))]
  rcases hB with ⟨h8, h2⟩ | ⟨h8, hout⟩
  · rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; exact h8)]; exact h2
  · rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [signInternal]
    rw [sMu_eq h₀' hK]
    exact hout

/-- Memory with the arguments `0`, `0x2000`, `0`, `0x2000`, `0`, `0x3000`,
`0x6000` and `0x10000` at `0x5004`. -/
def satMemS : Mem := fun a =>
  if a = 0x5009 then 0x20 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else
  if a = 0x501d then 0x60 else if a = 0x5022 then 1 else 0

/-- A state satisfying the precondition of `sign_message`. -/
def signSat (p : Params) : State :=
  Proof.MlKem.X86.satState satMemS [⟨0, p.skLen⟩, ⟨0x2000, 0⟩, ⟨0x2000, 0⟩, ⟨0x3000, 32⟩]
    [⟨0x6000, p.sigLen⟩, ⟨0x10000, mScrLen p⟩, ⟨0x5004, 32⟩]

theorem signMessage_sat (hp : p ∈ params) : ∃ s, (signMessageKContract p (plainKey p.skLen) X86.abi 176).pre s := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨signSat mlDsa44, by sig_sat_check [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩
  · exact ⟨signSat mlDsa65, by sig_sat_check [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩
  · exact ⟨signSat mlDsa87, by sig_sat_check [signMessageKContract, signMessageKSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, signSat, Proof.MlKem.X86.satState, satMemS]⟩

end

end VG.Proof.MlDsa.X86.Message
