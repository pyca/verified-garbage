module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide

meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
meta import VerifiedGarbage.TCB.Code
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step

/-!
# Deterministic ECDSA on PPC64LE: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frames' pushes and pops they are related by
`Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next piece
needs). The blocks address only the frame, from `sp`, and the buffers, from
pointers loaded from the frame, which agree (the taint analysis of the rest
of the block, from the registers that hold them: `two_split`); each call is
of constant-time code whose public data agree (`two_call`); and the loop's
branch agrees, since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

/-! ## Two runs -/

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : Rfc) := Lay P.I.hashLen → (Reg → BitVec 64) → Addr → Mem → State → Prop

/-- Two runs with the layout `L`, that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
structure TwoAt (P : Rfc) (Φ : Pred P) (L : Lay P.I.hashLen) (g₁ g₂ : Reg → BitVec 64) (lr₁ lr₂ : Addr)
    (m₁ m₂ : Mem) (a b : State) : Prop where
  ok : L.Ok
  q : L.q = P.c.len
  x : exitAt P L m₁ = exitAt P L m₂
  c₁ : Ctx L g₁ lr₁ m₁ a
  c₂ : Ctx L g₂ lr₂ m₂ b
  f₁ : Φ L g₁ lr₁ m₁ a
  f₂ : Φ L g₂ lr₂ m₂ b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : Rfc) (Φ : Pred P) (a b : State) : Prop :=
  ∃ L g₁ g₂ lr₁ lr₂ m₁ m₂, TwoAt P Φ L g₁ g₂ lr₁ lr₂ m₁ m₂ a b

variable {P : Rfc}

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → L.q = P.c.len → Ctx L g lr m₀ t →
      Φ L g lr m₀ t → WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ lr₁ m₁ s₁ h.ok h.q h.c₁ h.f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ lr₂ m₂ s₂ h.ok h.q h.c₂ h.f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.x, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- The taint check of a block, from the registers `rs` public. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- A block that addresses memory only from `sp`. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk [] is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => ⟨t.c₁.sp.trans t.c₂.sp.symm, fun r hr => by
      simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) h

/-- A block that loads pointers, the same in both runs, into `rs`, and then
addresses memory from them and `sp`. -/
theorem two_split {pre rest : List Instr} {Φ : Pred P} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hpre : TaintOk [] pre)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t →
      WP isa (.block pre) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ rs, t'.gpr r = f L r)
    (hrest : TaintOk rs rest) :
    RelCT isa (Two P Φ) (.block (pre ++ rest)) fun _ _ => True := by
  refine RelCT.block_append (RelCT.seq (R := fun (a b : State) => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) ?_ ?_)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨ht, -⟩ := two_blk (Φ := Φ) hpre _ _ _ _ _ _ hp e₁ e₂
    obtain ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ lr₁ m₁ s₁ h.ok h.c₁
    obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ lr₂ m₂ s₂ h.ok h.c₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, by rw [y₁.1, y₂.1, h.c₁.sp, h.c₂.sp], fun r hr => by rw [y₁.2 r hr, y₂.2 r hr]⟩
  · let ⟨_, h⟩ := hrest
    exact VG.RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ hp => ⟨hp.1, fun r hr =>
      hp.2 r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A block that addresses memory from `sp` and the registers `rs`, which
hold the same values in both runs. -/
theorem two_regs {is : List Instr} {Φ : Pred P} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hf : ∀ L g lr m₀ (t : State), Φ L g lr m₀ t → ∀ r ∈ rs, t.gpr r = f L r) (h : TaintOk rs is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => ⟨t.c₁.sp.trans t.c₂.sp.symm, fun r hr => by
      rw [hf _ _ _ _ _ t.f₁ r (Taint.mem_ofRegs.mp hr), hf _ _ _ _ _ t.f₂ r (Taint.mem_ofRegs.mp hr)]⟩) h

/-- A call of constant-time code whose preconditions hold in both runs and
whose public data agree. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {Φ : Pred P} (rd wr : Lay P.I.hashLen → List Region)
    (hpre : ∀ (L : Lay P.I.hashLen) g lr m₀ (u : State), L.Ok → L.q = P.c.len → Ctx L g lr m₀ u →
      Φ L g lr m₀ u → k.pre (u.callEntry.withRegions (rd L) (wr L)) ∧ Covers (rd L ++ wr L) (u.rd ++ u.wr) ∧
        Covers (wr L) u.wr)
    (hpub : ∀ L g₁ g₂ lr₁ lr₂ m₁ m₂ (u₁ u₂ : State), TwoAt P Φ L g₁ g₂ lr₁ lr₂ m₁ m₂ u₁ u₂ →
      k.pub (u₁.callEntry.withRegions (rd L) (wr L)) (u₂.callEntry.withRegions (rd L) (wr L))) :
    RelCT isa (Two P Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ =>
    let ⟨p₁, c₁, w₁⟩ := hpre L g₁ lr₁ m₁ s₁ h.ok h.q h.c₁ h.f₁
    let ⟨p₂, c₂, w₂⟩ := hpre L g₂ lr₂ m₂ s₂ h.ok h.q h.c₂ h.f₂
    ⟨rd L, wr L, rd L, wr L, p₁, p₂, hpub _ _ _ _ _ _ _ _ _ h, c₁, w₁, c₂, w₂⟩

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
def IA (P : Rfc) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .r5 = L.B + BitVec.ofNat 64 128 ∧ u.gpr .r6 = BitVec.ofNat 64 P.K.H.D ∧
    u.gpr .r7 = L.scr + BitVec.ofNat 64 384

theorem init_pub {L : Lay P.I.hashLen} {g₁ g₂ : Reg → BitVec 64} {lr₁ lr₂ : Addr} {m₁ m₂ : Mem}
    {u₁ u₂ : State} (h : TwoAt P (IA P) L g₁ g₂ lr₁ lr₂ m₁ m₂ u₁ u₂) (rd wr : List Region) :
    (Proof.Hmac.Instance.initScratchContract P.K.I PPC64LE.abi (P.K.kI + 1)).pub (u₁.callEntry.withRegions rd wr)
      (u₂.callEntry.withRegions rd wr) := by
  sig_pub [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
    Proof.Hmac.initScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1],
    by rw [h.f₁.2.2.1, h.f₂.2.2.1], by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2]⟩

variable {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- HMAC's `init`'s regions. -/
abbrev initRd (P : Rfc) (L : Lay P.I.hashLen) : List Region := [⟨L.B + BitVec.ofNat 64 128, P.K.H.D⟩]
abbrev initWr (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 192, P.K.H.S⟩,
    ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩]

theorem initAt {L : Lay P.I.hashLen} (hL : L.Ok) {u : State} (hcu : Ctx L g lr m₀ u) (ha : IA P L g lr m₀ u) :
    (Proof.Hmac.Instance.initScratchContract P.K.I PPC64LE.abi (P.K.kI + 1)).pre (u.callEntry.withRegions (initRd P L) (initWr P L)) ∧
      Covers (initRd P L ++ initWr P L) (u.rd ++ u.wr) ∧ Covers (initWr P L) u.wr := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.K.hS
  have hD := P.K.hH.hD64
  have hDB := P.K.hH.hDB
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have kS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, P.K.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by omega_arith) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine ⟨initPre P.K h3 h4 h5 (by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]) h7
    (by rw [P.K.hIS, P.K.hH.hB]; exact hDB)
    (dS (by omega_arith) (by omega_arith) (by omega_arith)) (kS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith))
    (kS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith)) (kS (by omega_arith))
    (by rw [hsp, hL.sp_toNat]; omega_arith) (bS (by omega_arith)) (bS (by omega_arith))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (bS (by omega_arith))
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith), ?_, ?_⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩

theorem init_ct :
    RelCT isa (Two P (IA P)) (.call P.K.hm.initN P.K.hm.initC) fun _ _ => True :=
  two_call P.K.initV P.K.initCT (initRd P) (initWr P) (fun _ _ _ _ _ hL _ hc ha => initAt hL hc ha)
    fun _ _ _ _ _ _ _ _ _ h => init_pub h _ _

/-! ## The streaming `update` -/

/-- The arguments of the streaming `update`, for the data at `da L` of `len` bytes. -/
def UA (P : Rfc) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = BitVec.ofNat 64 P.K.H.B ∧ u.gpr .r5 = da L ∧
    u.gpr .r6 = BitVec.ofNat 64 len ∧ u.gpr .r7 = L.scr + BitVec.ofNat 64 384

abbrev updRd (da : Lay P.I.hashLen → Addr) (len : Nat) (L : Lay P.I.hashLen) : List Region := [⟨da L, len⟩]
abbrev updWr (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩]

theorem updAt {da : Lay P.I.hashLen → Addr} {len : Nat} {L : Lay P.I.hashLen} (hL : L.Ok) {u : State}
    (hcu : Ctx L g lr m₀ u) (ha : UA P da len L g lr m₀ u) (hd : DataOk L (da L) len) :
    (Proof.Hmac.Stream.PPC64LE.updK P.K.H.S P.K.H.W P.K.hH.SH.Repr).pre
        (u.callEntry.withRegions (updRd da len L) (updWr P L)) ∧
      Covers (updRd da len L ++ updWr P L) (u.rd ++ u.wr) ∧ Covers (updWr P L) u.wr := by
  obtain ⟨h3, -, h5, h6, h7⟩ := ha
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.K.hS
  have hW := P.K.hW
  simp only [sWork, sMsg] at hW
  have hl := hd.len_le
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 48).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below48]; exact hL.stk_scr (by omega_arith) h
  have c3 : u.callEntry.gpr .r3 = L.scr + BitVec.ofNat 64 0 := (State.callEntry_gpr _ (by decide)).trans h3
  have c5 : u.callEntry.gpr .r5 = da L := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : (u.callEntry.gpr .r6).toNat = len := by
    rw [State.callEntry_gpr _ (by decide), h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
  have c7 : u.callEntry.gpr .r7 = L.scr + BitVec.ofNat 64 384 := (State.callEntry_gpr _ (by decide)).trans h7
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Hmac.Stream.PPC64LE.updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c5, c6, c7]
    exact ⟨trivial, trivial, dS (by omega_arith) (by omega_arith) (by omega_arith), hd.scr hL (by omega_arith), hd.scr hL (by omega_arith),
      by rw [hsp, hL.sp_toNat]; omega_arith, bS (by omega_arith), by rw [hsp, L.below48]; exact hd.low hL (by omega_arith),
      bS (by omega_arith)⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.within
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩

theorem upd_ct {da : Lay P.I.hashLen → Addr} {len : Nat} (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len) :
    RelCT isa (Two P (UA P da len)) (.call P.K.hm.updN P.K.hm.updC) fun _ _ => True :=
  two_call P.K.hH.upd P.K.updCT (updRd da len) (updWr P)
    (fun L _ _ _ _ hL _ hc ha => updAt hL hc ha (hd L hL)) fun L _ _ _ _ _ _ u₁ u₂ h => by
      simp only [Proof.Hmac.Stream.PPC64LE.updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
        State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
        State.callEntry_gpr _ (show Reg.r7 ∉ linkRegs by decide)]
      exact ⟨by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1], by rw [h.f₁.2.2.1, h.f₂.2.2.1],
        by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2], by rw [h.c₁.sp, h.c₂.sp]⟩

/-! ## HMAC's `finalize` -/

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC to `dst`. -/
def FA (P : Rfc) (len dst : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .r5 = BitVec.ofNat 64 (P.K.H.B + len) ∧ u.gpr .r6 = L.B + BitVec.ofNat 64 (96 + dst) ∧
    u.gpr .r7 = L.scr + BitVec.ofNat 64 384

abbrev finRd (P : Rfc) (L : Lay P.I.hashLen) : List Region := [⟨L.scr + BitVec.ofNat 64 192, P.K.H.S⟩]
abbrev finWr (P : Rfc) (dst : Nat) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩, ⟨L.B + BitVec.ofNat 64 (96 + dst), P.K.H.D⟩,
    ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩]

theorem finAt {len dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216) {L : Lay P.I.hashLen} (hL : L.Ok) {u : State}
    (hcu : Ctx L g lr m₀ u) (ha : FA P len dst L g lr m₀ u) :
    (Proof.Hmac.Instance.finalizeScratchContract P.K.I PPC64LE.abi (P.K.kF + 1)).pre
        (u.callEntry.withRegions (finRd P L) (finWr P dst L)) ∧
      Covers (finRd P L ++ finWr P dst L) (u.rd ++ u.wr) ∧ Covers (finWr P dst L) u.wr := by
  obtain ⟨h3, h4, -, h6, h7⟩ := ha
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.K.hS
  have hD := P.K.hH.hD64
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have oS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (96 + dst), P.K.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by omega_arith) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine ⟨finPre P.K (inner := L.scr + BitVec.ofNat 64 0) (outer := L.scr + BitVec.ofNat 64 192)
    (out := L.B + BitVec.ofNat 64 (96 + dst)) (scr := L.scr + BitVec.ofNat 64 384) h3 h4 h6 h7
    (dS (by omega_arith) (by omega_arith) (by omega_arith)) (oS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith))
    (oS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith)) (oS (by omega_arith))
    (by rw [hsp, hL.sp_toNat]; omega_arith) (bS (by omega_arith)) (bS (by omega_arith))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (bS (by omega_arith))
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith), ?_, ?_⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩

theorem fin_ct {len dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216) :
    RelCT isa (Two P (FA P len dst)) (.call P.K.hm.finN P.K.hm.finC) fun _ _ => True :=
  two_call P.K.finV P.K.finCT (finRd P) (finWr P dst) (fun _ _ _ _ _ hL _ hc ha => finAt hdst hL hc ha)
    fun _ _ _ _ _ _ _ u₁ u₂ h => by
      sig_pub [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
        Proof.Hmac.finalizeScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
      exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1],
        by rw [h.f₁.2.2.1, h.f₂.2.2.1], by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2]⟩

/-! ## The blocks -/

/-- The registers that hold the message's pointers: `scratch`, `d` and the
frame, and, if `wide`, `digest`. -/
abbrev msgRegs (wide : Bool) : List Reg := if wide then [.r7, .r9, .r10, .r11] else [.r9, .r10, .r11]

/-- If two `V`s make a candidate: the digest for `core`, from `digest` in `r9`,
`V` kept, and the candidate's next eight bytes; and the conversions, from
`scratch` in `r3`. -/
structure WideBlks (c : Cfg) : Prop where
  dig : TaintOk [.r9, .r11] (([.li .r8 0, .store .d .r8 .r11 (fX + c.H.D)] : List Instr) ++
    Cfg.copyW (c.H.D / 4) .r9 0 .r11 fX)
  conv₁ : TaintOk [.r3] (c.convBody fX (8 * (c.len - c.H.D) - c.sh))
  keep : TaintOk [] c.keepV
  top : TaintOk [] [.addSp .r11 0, .load .d .r8 .r11 fV, .store .d .r8 .r11 (fKb + c.H.D)]
  conv₂ : TaintOk [.r3] (c.convBody fKb c.sh)

/-- The blocks that depend on the instance's sizes, each of which addresses
memory only from `sp` or from the pointers loaded before it: their taint
checks, of the instance's code. -/
structure Blks (K : Kit) (c : Cfg) : Prop where
  a₁ : TaintOk [] (Cfg.hmacArgs₁ K.H.D)
  a₂V : TaintOk [] (Cfg.hmacArgs₂ K.H.B [.addSp .r5 fV] K.H.D)
  a₂F : TaintOk [] (Cfg.hmacArgs₂ K.H.B [.addi .r5 .r12 sMsg] (K.H.D + 2 * c.len + 1))
  a₂R : TaintOk [] (Cfg.hmacArgs₂ K.H.B [.addi .r5 .r12 sMsg] (K.H.D + 1))
  a₃V : TaintOk [] (Cfg.hmacArgs₃ K.H.B K.H.D fV)
  a₃F : TaintOk [] (Cfg.hmacArgs₃ K.H.B (K.H.D + 2 * c.len + 1) fK)
  a₃R : TaintOk [] (Cfg.hmacArgs₃ K.H.B (K.H.D + 1) fK)
  m₀ : TaintOk (msgRegs c.wide) (Cfg.msg c.len K.H.D 0 true c.fHo c.wide)
  m₁ : TaintOk (msgRegs c.wide) (Cfg.msg c.len K.H.D 1 true c.fHo c.wide)
  mR : TaintOk [.r9, .r10, .r11] (Cfg.msg c.len K.H.D 0 false)
  red : c.wide = false → TaintOk [.r9, .r11] (c.reduce.drop 2 ++ Cfg.initKV)
  wide : c.wide = true → WideBlks c
  cnt : TaintOk [] c.initCnt

theorem msgPtrs_blk (wide : Bool) : TaintOk [] (Cfg.msgPtrs wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
theorem coreArgs_blk (wide : Bool) : TaintOk [] (Cfg.coreArgs wide) := by
  cases wide
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
theorem goOn_blk : TaintOk [] Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk [] Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk [] Cfg.stop := ⟨_, by taint_decide⟩
theorem wipe_blk (b w : Bool) : TaintOk [] (Cfg.wipe b w) := by
  cases b <;> cases w
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
theorem initKV_blk : TaintOk [] Cfg.initKV := ⟨_, by taint_decide⟩
theorem ldScr_blk : TaintOk [] [.addSp .r11 0, .load .d .r3 .r11 fScratch] := ⟨_, by taint_decide⟩
theorem saveArgs_blk : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩
theorem redPre_blk : TaintOk [] [.addSp .r11 0, .load .d .r9 .r11 fDigest] := ⟨_, by taint_decide⟩

/-! ## One HMAC -/

/-- After HMAC's `init` and `update`: the states, for the state before. -/
def Ini (P : Rfc) : Pred P := fun L g lr m₀ u => ∃ t, Inited P.K L g lr m₀ t u
def Upt (P : Rfc) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pred P :=
  fun L g lr m₀ u => ∃ t, Updated P.K L g lr m₀ t (da L) len u

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, and its
calls are constant time with arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {len dst : Nat} {Φ : Pred P}
    (hdA : ∀ (L : Lay P.I.hashLen) g lr m₀, L.Ok → ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr →
      WP isa (.block dataA) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da L)
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len) (hlen : P.K.H.B + len < 2 ^ 15)
    (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
    (a₁ : TaintOk [] (Cfg.hmacArgs₁ P.K.H.D)) (a₂ : TaintOk [] (Cfg.hmacArgs₂ P.K.H.B dataA len))
    (a₃ : TaintOk [] (Cfg.hmacArgs₃ P.K.H.B len dst)) :
    RelCT isa (Two P Φ) (P.c.hmac dataA len dst) fun _ _ => True := by
  have hD := P.K.hH.hD64
  rw [Cfg.hmac, P.hcH]
  have iS : RelCT isa (Two P Φ) (.seq (.block (Cfg.hmacArgs₁ P.K.H.D)) (.call P.K.hm.initN P.K.hm.initC))
      (Two P (Ini P)) :=
    two_wp ((two_wp (Ψ := IA P) (two_blk a₁) fun L _ _ _ _ hL _ hc _ =>
        WP.mono (args₁_ok hL hc (D := P.K.H.D) (by omega_arith)) fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq init_ct)
      fun _ _ _ _ t hL _ hc _ => WP.mono (init_step P.K hL hc) fun _ h => ⟨h.ctx, t, h⟩
  have uS : RelCT isa (Two P (Ini P)) (.seq (.block (Cfg.hmacArgs₂ P.K.H.B dataA len))
      (.call P.K.hm.updN P.K.hm.updC)) (Two P (Upt P da len)) :=
    two_wp ((two_wp (Ψ := UA P da len) (two_blk a₂) fun L g lr m₀ _ hL _ hc _ =>
        WP.mono (args₂_ok hL hc (B := P.K.H.B) (by omega_arith) (len := len) (by omega_arith) (hdA L g lr m₀ hL))
          fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq (upd_ct hd))
      fun L g lr m₀ _ hL _ _ ⟨t, hi⟩ => WP.mono (upd_step P.K hL hi (hd L hL) (by omega_arith) (hdA L g lr m₀ hL))
        fun _ h => ⟨h.ctx, t, h⟩
  have fS : RelCT isa (Two P (Upt P da len)) (.seq (.block (Cfg.hmacArgs₃ P.K.H.B len dst))
      (.call P.K.hm.finN P.K.hm.finC)) fun _ _ => True :=
    (two_wp (Ψ := FA P len dst) (two_blk a₃) fun _ _ _ _ _ hL _ hc _ =>
      WP.mono (args₃_ok hL hc (B := P.K.H.B) (len := len) (by omega_arith) (by omega_arith)) fun _ ⟨c, _, _, a⟩ =>
        ⟨c, a⟩).seq (fin_ct hdst)
  exact RelCT.assoc (iS.seq (RelCT.assoc (uS.seq fS)))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct (B : Blks P.K P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.hmacV fun _ _ => True := by
  have hD := P.K.hH.hD64
  have hB : P.K.H.B ≤ 128 := by rcases P.K.hH.dims.B with h | h <;> omega_arith
  rw [Cfg.hmacV, P.hcH]
  exact hmac_ct (da := fun L => L.B + BitVec.ofNat 64 192) (len := P.K.H.D) (dst := 96)
    (fun _ _ _ _ _ _ hc _ => dataV_ok hc _ rfl) (fun _ _ => .inl ⟨192, rfl, by omega_arith, by omega_arith⟩)
    (by omega_arith) ⟨by omega_arith, by omega_arith⟩ B.a₁ B.a₂V B.a₃V

/-- The pointers `msgPtrs` loads. -/
def msgP (L : Lay P.I.hashLen) : Reg → BitVec 64
  | .r7 => L.dg
  | .r9 => L.scr
  | .r10 => L.d
  | _ => L.B + BitVec.ofNat 64 96

theorem msgPtrs_two (L : Lay P.I.hashLen) (wide : Bool) {g lr m₀} {t : State} (hL : L.Ok)
    (hc : Ctx L g lr m₀ t) :
    WP isa (.block (Cfg.msgPtrs wide)) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ msgRegs wide, t'.gpr r = msgP L r := by
  cases wide
  · exact WP.mono (msgPtrs_ok hL hc) fun _ ⟨c, _, _, h11, h9, h10⟩ => ⟨c.sp.trans hc.sp.symm, fun r hr => by
      simp only [msgRegs, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h9
      · exact h10
      · exact h11⟩
  · exact WP.mono (msgPtrsW_ok hL hc) fun _ ⟨c, _, _, h11, h9, h10, h7⟩ => ⟨c.sp.trans hc.sp.symm, fun r hr => by
      simp only [msgRegs, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h7
      · exact h9
      · exact h10
      · exact h11⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct (B : Blks P.K P.c) {Φ : Pred P} {b : Nat} {full wide : Bool} {len ho : Nat}
    (hlen : len ≤ 197)
    (hmsg : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → L.q = P.c.len → Ctx L g lr m₀ t →
      WP isa (.block (Cfg.msgPtrs wide ++ Cfg.msg P.c.len P.K.H.D b full ho wide)) t fun u => Ctx L g lr m₀ u)
    (tm : TaintOk (msgRegs wide) (Cfg.msg P.c.len P.K.H.D b full ho wide))
    (t₂ : TaintOk [] (Cfg.hmacArgs₂ P.K.H.B [.addi .r5 .r12 sMsg] len))
    (t₃ : TaintOk [] (Cfg.hmacArgs₃ P.K.H.B len fK)) :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.msgPtrs wide ++ Cfg.msg P.c.len P.K.H.D b full ho wide))
      (.seq (P.c.hmac [.addi .r5 .r12 sMsg] len fK) P.c.hmacV)) fun _ _ => True := by
  have hD := P.K.hH.hD64
  have hB : P.K.H.B ≤ 128 := by rcases P.K.hH.dims.B with h | h <;> omega_arith
  refine (two_wp (Ψ := fun _ _ _ _ _ => True) (two_split (Φ := Φ) (msgRegs wide) msgP (msgPtrs_blk wide)
    (fun L _ _ _ _ hL hc => msgPtrs_two L wide hL hc) tm) fun L _ _ _ _ hL hLq hc _ =>
      WP.mono (hmsg L _ _ _ _ hL hLq hc) fun _ h => ⟨h, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ _ _ => True)
    (hmac_ct (da := fun L => L.scr + BitVec.ofNat 64 2256) (len := len) (dst := 32)
      (fun _ _ _ _ _ _ _ hr => dataM_ok _ hr) (fun _ _ => .inr ⟨2256, rfl, by omega_arith, by omega_arith⟩)
      (by omega_arith) ⟨by omega_arith, by omega_arith⟩ B.a₁ t₂ t₃)
    fun L _ _ _ _ hL hLq hc _ => by
      refine WP.mono (hmac_ok P.K P.hcH hL hc (dataA := [.addi .r5 .r12 sMsg]) (da := L.scr + BitVec.ofNat 64 2256)
        (len := len) (dst := 32) (.inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) (by omega_arith) ⟨by omega_arith, by omega_arith⟩
        fun u _ hr => dataM_ok u hr) fun _ h => ⟨h.ctx, trivial⟩).seq (hmacV_ct B)

theorem rekeyFull_ct (B : Blks P.K P.c) {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) (P.c.rekeyFull b) fun _ _ => True := by
  rw [Cfg.rekeyFull, P.hcH]
  have hmsg : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → L.q = P.c.len → Ctx L g lr m₀ t →
      WP isa (.block (Cfg.msgPtrs P.c.wide ++ Cfg.msg P.c.len P.K.H.D b true P.c.fHo P.c.wide)) t
        fun u => Ctx L g lr m₀ u := fun L g lr m₀ t hL hq hc => by
    rw [← wideL hq, L.fHo_eq hq.symm P.hcD, ← hq]
    exact WP.mono (msgFull_ok P.K hL P.hD.symm (fun hw => ⟨lq_ok hq hw, (narrow_q hq hw).2.1⟩)
      (fun hw => Nat.le_of_eq (wide_q hq hw).1) hc hb) fun _ h => h.1
  have hl : P.K.H.D + 2 * P.c.len + 1 ≤ 197 := by
    have := P.K.hH.hD64
    cases hw : P.c.wide
    · have := P.hk16 hw; have := P.hk hw; omega_arith
    · have := (P.hW hw).2.1; omega_arith
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_arith
  · exact rekey_gen_ct B (full := true) hl hmsg B.m₀ B.a₂F B.a₃F
  · exact rekey_gen_ct B (full := true) hl hmsg B.m₁ B.a₂F B.a₃F

theorem rekey_ct (B : Blks P.K P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.rekey fun _ _ => True := by
  rw [Cfg.rekey, P.hcH]
  have hD := P.K.hH.hD64
  have hD4 := P.K.hH.hD4
  have hmsg : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → L.q = P.c.len → Ctx L g lr m₀ t →
      WP isa (.block (Cfg.msgPtrs false ++ Cfg.msg P.c.len P.K.H.D 0 false fH false)) t
        fun u => Ctx L g lr m₀ u := fun L g lr m₀ t hL hq hc => by
    rw [← hq]
    exact WP.mono (msg_ok hL hc (D := P.K.H.D) (b := 0) false fH hD4 hD (fun h => nomatch h)
      (fun h => nomatch h) (fun h => nomatch h) (fun h => nomatch h) (by omega_arith)) fun _ h => h.1
  exact rekey_gen_ct B (b := 0) (full := false) (wide := false) (len := P.K.H.D + 1) (by omega_arith) hmsg B.mR B.a₂R
    B.a₃R

/-! ## The conversions and the candidate -/

/-- `scratch` in `r3`. -/
def ScrIn (P : Rfc) : Pred P := fun L _ _ _ u => u.gpr .r3 = L.scr

/-- A conversion: its block addresses memory from `scratch`, loaded first, and `sp`. -/
theorem conv_ct {Φ : Pred P} {o s : Nat} (h : TaintOk [.r3] (P.c.convBody o s)) :
    RelCT isa (Two P Φ) (P.c.conv o s) fun _ _ => True :=
  (two_wp (Ψ := ScrIn P) (two_blk ldScr_blk) fun _ _ _ _ _ hL _ hc _ => ldScr_ok hL hc).seq
    (two_regs [.r3] (fun L _ => L.scr) (fun _ _ _ _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) h)

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct (B : Blks P.K P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.cand fun _ _ => True := by
  cases hw : P.c.wide
  · rw [show P.c.cand = P.c.hmacV by simp only [Cfg.cand, hw, Bool.false_eq_true, ite_false]]
    exact hmacV_ct B
  · have W := B.wide hw
    obtain ⟨hcD, hcl, -⟩ := P.hW hw
    simp only [Cfg.cand, Cfg.candTop, hw, ite_true]
    have he : ∀ {L : Lay P.I.hashLen}, L.q = P.c.len → L.e = 144 := fun hq =>
      (wide_q hq ((wideL hq).trans hw)).2.2.1
    refine (two_wp (Ψ := fun _ _ _ _ _ => True) (hmacV_ct B) fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (hmacV_ok P.K P.hcH hL (lfar hq) hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := fun _ _ _ _ _ => True) (two_blk W.keep) fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (keepV_ok hL hcD (he hq) hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := fun _ _ _ _ _ => True) (hmacV_ct B) fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (hmacV_ok P.K P.hcH hL (lfar hq) hc) fun _ h => ⟨h.1, trivial⟩).seq ?_
    exact (two_wp (Ψ := fun _ _ _ _ _ => True) (two_blk W.top) fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (top_ok hL hcD (he hq) hc) fun _ h => ⟨h.1, trivial⟩).seq (conv_ct W.conv₂)

/-! ## One candidate -/

abbrev coreRd (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.d, P.R.E.curve.len⟩, ⟨dgAddr L, P.R.E.curve.len⟩, ⟨kAddr L, P.R.E.curve.len⟩]
abbrev coreWr (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.out, 2 * P.R.E.curve.len⟩, ⟨L.scr, 8192⟩]

theorem coreAt {L : Lay P.I.hashLen} (hL : L.Ok) (hq : L.q = P.c.len) {u : State} (hc : Ctx L g lr m₀ u)
    (ha : CoreRegs L u) :
    (Proof.Ecdsa.Instance.signContract P.R.E PPC64LE.abi).pre (u.callEntry.withRegions (coreRd P L) (coreWr P L)) ∧
      Covers (coreRd P L ++ coreWr P L) (u.rd ++ u.wr) ∧ Covers (coreWr P L) u.wr := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  have hQ : P.R.E.curve.len = L.q := by rw [← P.hcl, hq]
  obtain ⟨o₁, o₂, o₃, o₄, c₁, c₂, c₃, n₁, n₂, n₃, n₄, n₅, hcov⟩ := core_regions hL hq
  refine ⟨corePre P.R h3 h4 h5 h6 h7 (by rw [hQ]; exact o₁) (by rw [hQ]; exact o₂) (by rw [hQ]; exact o₃)
    (by rw [hQ]; exact o₄) (by rw [hQ]; exact c₁) (by rw [hQ]; exact c₂) (by rw [hQ]; exact c₃)
    (by rw [hQ]; exact n₁) (by rw [hQ]; exact n₂) (by rw [hQ]; exact n₃) (by rw [hQ]; exact n₄) n₅, ?_, ?_⟩
  · simp only [coreRd, coreWr, hQ]
    exact hc.covers hcov
  · simp only [coreWr, hQ]
    refine hc.coversW fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩

theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u) (.call P.c.coreN P.c.coreC)
      fun _ _ => True := by
  rw [P.hcN, P.hcC]
  exact two_call P.R.V P.R.ct (coreRd P) (coreWr P) (fun _ _ _ _ _ hL hq hc ha => coreAt hL hq hc ha.2)
    fun _ _ _ _ _ _ _ u₁ u₂ h => by
      obtain ⟨-, a3, a4, a5, a6, a7⟩ := h.f₁
      obtain ⟨-, b3, b4, b5, b6, b7⟩ := h.f₂
      sig_pub [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
        PPC64LE.abi, PPC64LE.argRegs, stackBelow]
      exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [a3, b3], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6],
        by rw [a7, b7]⟩

/-- After a candidate: whether to go on, and what the next piece needs. -/
def After (P : Rfc) (i : Nat) : Pred P := fun L _ _ m₀ t =>
  isa.eval (.nonzero .d .r12) t = some (decide (i < exitAt P L m₀)) ∧
    ((i < exitAt P L m₀ ∧ LoopInv P L m₀ (i + 1) t) ∨ (¬ i < exitAt P L m₀ ∧ Exit P L m₀ i t))

theorem tryOne_ct (B : Blks P.K P.c) {i : Nat} :
    RelCT isa (Two P fun L _ _ m₀ u => LoopInv P L m₀ i u) P.c.tryOne (Two P (After P i)) := by
  refine two_wp ?_ fun L g lr m₀ t hL hq hc hi => WP.mono (tryOne_ok hL hq hc hi) fun t' ⟨hc', h⟩ => ⟨hc', ?_⟩
  · rw [Cfg.tryOne]
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₁ P L m₀ i u) (cand_ct B) fun L g lr m₀ t hL hq hc hi =>
      try₁_ok hL hq hc hi).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u) (two_blk (coreArgs_blk _))
      fun L g lr m₀ t hL hq hc hi => try₂_ok hL hq hc hi).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₃ P L m₀ i u) core_ct
      fun L g lr m₀ t hL hq hc hi => try₃_ok hL hq hc hi.1 hi.2).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
      fun L g lr m₀ t hL hq hc hi => try₄_ok hL hq hc hi).seq ?_
    refine RelCT.ite (fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ => ?_) ?_ ?_
    · rw [h.f₁.dec, h.f₂.dec]
      refine congrArg some (decide_eq_decide.mpr ?_)
      rw [go_iff h.q h.f₁.lt h.f₁.fails, go_iff h.q h.f₂.lt h.f₂.fails, h.x]
    · refine RelCT.mono (P := Two P fun L _ _ m₀ u => Mid P L m₀ i u) ?_ (fun _ _ h => h.1) fun _ _ h => h
      exact (two_wp (Ψ := fun _ _ _ _ _ => True) (rekey_ct B) fun L g lr m₀ t hL hq hc _ =>
        WP.mono (rekey_ok P.K P.hcH hq.symm hL (lfar hq) (by have := lq_le hq; omega_arith) hc)
          fun _ h => ⟨h.ctx, trivial⟩).seq (two_blk again_blk)
    · exact RelCT.mono (two_blk stop_blk) (fun _ _ h => h.1) fun _ _ h => h
  · rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
    · have hn : ¬ i < exitAt P L m₀ := fun hlt => by
        have := (go_iff hq hx.lt hx.fails).mpr hlt
        rcases hx.last with h | h
        · exact h this.1
        · omega
      exact ⟨by rw [he]; simp [hn], .inr ⟨hn, hx⟩⟩
    · have hn : i < exitAt P L m₀ :=
        (go_iff hq (by have := hx.lt; omega_arith) fun j hj => hx.fails j (by omega_arith)).mp
          ⟨hx.fails i (by omega_arith), hx.lt⟩
      exact ⟨by rw [he]; simp [hn], .inl ⟨hn, hx⟩⟩

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g lr m₀ t, Φ L g lr m₀ t → Ψ L g lr m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t⟩ := ht
  ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t.ok, t.q, t.x, t.c₁, t.c₂, h _ _ _ _ _ t.f₁, h _ _ _ _ _ t.f₂⟩

/-! ## The loop -/

theorem loop_ct (B : Blks P.K P.c) :
    RelCT isa (Two P fun L _ _ m₀ u => LoopInv P L m₀ 0 u) (.loop P.c.tryOne (.nonzero .d .r12))
      (Two P fun L _ _ m₀ u => ∃ i, Exit P L m₀ i u) := by
  refine RelCT.mono (RelCT.loop (I := fun n => Two P fun L _ _ m₀ u => LoopInv P L m₀ (P.c.tries - n) u ∧
    n ≤ P.c.tries) (fun n => ?_) P.c.tries) (fun _ _ h => Two.mono (fun _ _ _ _ _ hi => ⟨by
      rw [Nat.sub_self]; exact hi, Nat.le_refl _⟩) h) fun _ _ h => h
  by_cases hn : n ≤ P.c.tries
  · refine RelCT.mono (tryOne_ct B (i := P.c.tries - n)) (fun _ _ h => Two.mono (fun _ _ _ _ _ hi => hi.1) h)
      fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ => ⟨by rw [h.f₁.1, h.f₂.1, h.x], fun he => ?_, fun he => ?_⟩
    · rw [h.f₁.1] at he
      have hx : ¬ P.c.tries - n < exitAt P L m₁ := by simpa using he
      have hx' : ¬ P.c.tries - n < exitAt P L m₂ := by rw [← h.x]; exact hx
      refine ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.x, h.c₁, h.c₂, ?_, ?_⟩
      · rcases h.f₁.2 with ⟨h', -⟩ | ⟨-, hx₁⟩
        · exact absurd h' hx
        · exact ⟨_, hx₁⟩
      · rcases h.f₂.2 with ⟨h', -⟩ | ⟨-, hx₂⟩
        · exact absurd h' hx'
        · exact ⟨_, hx₂⟩
    · rw [h.f₁.1] at he
      have hx : P.c.tries - n < exitAt P L m₁ := by simpa using he
      have hx' : P.c.tries - n < exitAt P L m₂ := by rw [← h.x]; exact hx
      obtain ⟨-, i₁⟩ | ⟨h', -⟩ := h.f₁.2
      · obtain ⟨-, i₂⟩ | ⟨h', -⟩ := h.f₂.2
        · have := i₁.lt
          refine ⟨n - 1, by omega_arith, L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.x, h.c₁, h.c₂, ⟨?_, by omega_arith⟩,
            ⟨?_, by omega_arith⟩⟩
          · rwa [show P.c.tries - (n - 1) = P.c.tries - n + 1 by omega_arith]
          · rwa [show P.c.tries - (n - 1) = P.c.tries - n + 1 by omega_arith]
        · exact absurd hx' h'
      · exact absurd hx h'
  · exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => hn h.f₁.2

/-! ## Steps a–g and the loop -/

/-- The digest's pointer and the frame. -/
def redP (L : Lay P.I.hashLen) : Reg → BitVec 64
  | .r9 => L.dg
  | _ => L.B + BitVec.ofNat 64 96

theorem redPre_two (L : Lay P.I.hashLen) {g lr m₀} {t : State} (hL : L.Ok) (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r9 .r11 fDigest]) t fun t' => t'.sp = t.sp ∧
      ∀ r ∈ [Reg.r9, .r11], t'.gpr r = redP L r := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (by rw [k₁.rd, k₁.wr]; exact hc.inFr (by omega_arith) (by omega_arith)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨by rw [k₂.sp, k₁.sp],
      fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [v₂, m₁, hc.pDg]; rfl
  · rw [k₂.gpr _ (by decide), hb]; rfl

theorem reduce_split (c : Cfg) :
    c.reduce ++ Cfg.initKV = ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ (c.reduce.drop 2 ++ Cfg.initKV) := by
  rw [← List.append_assoc]
  congr 1

theorem coreDigest_split (c : Cfg) :
    (([.addSp .r11 0, .load .d .r9 .r11 fDigest, .li .r8 0, .store .d .r8 .r11 (fX + c.H.D)] : List Instr) ++
      Cfg.copyW (c.H.D / 4) .r9 0 .r11 fX) =
    ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++
      (([.li .r8 0, .store .d .r8 .r11 (fX + c.H.D)] : List Instr) ++ Cfg.copyW (c.H.D / 4) .r9 0 .r11 fX) := rfl

/-- `h`, or the digest for `core`, and `K` and `V`. -/
theorem start_ct (B : Blks P.K P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.start fun _ _ => True := by
  cases hw : P.c.wide
  · simp only [Cfg.start, hw, Bool.false_eq_true, ite_false]
    rw [reduce_split]
    exact two_split [.r9, .r11] redP redPre_blk (fun L _ _ _ _ hL hc => redPre_two L hL hc) (B.red hw)
  · have W := B.wide hw
    obtain ⟨hcD, hcl, -⟩ := P.hW hw
    have he : ∀ {L : Lay P.I.hashLen}, L.q = P.c.len → L.e = 144 := fun hq =>
      (wide_q hq ((wideL hq).trans hw)).2.2.1
    have hdn : ∀ {L : Lay P.I.hashLen}, L.q = P.c.len → 64 ≤ P.I.hashLen := fun hq =>
      Nat.le_of_eq (wide_q hq ((wideL hq).trans hw)).2.1.symm
    simp only [Cfg.start, hw, ite_true]
    refine (two_wp (Ψ := fun _ _ _ _ _ => True) ?_ fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (coreDigest_ok hL hcl hcD (P.hcw hw) (P.hsh hw) (he hq) (hdn hq) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk initKV_blk)
    rw [Cfg.coreDigest]
    refine (two_wp (Ψ := fun _ _ _ _ _ => True) ?_ fun _ _ _ _ _ hL hq hc _ =>
      WP.mono (dig_ok hL hcD (he hq) (hdn hq) hc) fun _ h => ⟨h.1, trivial⟩).seq (conv_ct W.conv₁)
    rw [coreDigest_split]
    exact two_split [.r9, .r11] redP redPre_blk (fun L _ _ _ _ hL hc => redPre_two L hL hc) W.dig

theorem rest_ct (B : Blks P.K P.c) :
    RelCT isa (Two P fun _ _ _ _ _ => True)
      (.seq P.c.start (.seq (P.c.rekeyFull 0) (.seq (P.c.rekeyFull 1)
        (.seq (.block P.c.initCnt) (.seq (.loop P.c.tryOne (.nonzero .d .r12))
          (.block (Cfg.wipe P.c.hHigh P.c.wide)))))))
      fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ _ m₀ u => QA P L m₀ u) (start_ct B)
    fun L g lr m₀ t hL hq hc _ => stageA_ok hL hq hc).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => QB P L m₀ (K₁ P L m₀) (V₁ P L m₀) u) (rekeyFull_ct B 0 (by decide))
    fun L g lr m₀ t hL hq hc ha => stageB_ok hL hq hc ha).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => QB P L m₀ (kv0 P L m₀).1 (kv0 P L m₀).2 u)
    (rekeyFull_ct B 1 (by decide)) fun L g lr m₀ t hL hq hc hb => stageC_ok hL hq hc hb).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => LoopInv P L m₀ 0 u) (two_blk B.cnt)
    fun L g lr m₀ t hL hq hc hb => stageD_ok hL hq hc hb).seq ?_
  exact (loop_ct B).seq (two_blk (wipe_blk _ _))

/-! ## The whole function -/

/-- Two runs whose public data agree, as the contract says. -/
def Pre2 (P : Rfc) (s₁ s₂ : State) : Prop :=
  (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pre s₁ ∧ (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pre s₂ ∧
    (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pub s₁ s₂

/-- In the inner frame's body. -/
def Entered (P : Rfc) (a b : State) : Prop :=
  ∃ σ₁ σ₂, Pre2 P σ₁ σ₂ ∧ a = entered (extra P.c.hHigh P.c.wide) σ₁ ∧ b = entered (extra P.c.hHigh P.c.wide) σ₂

theorem lay_eq {σ₁ σ₂ : State} (h : Pre2 P σ₁ σ₂) :
    lay P.I.hashLen P.I.ecdsa.curve.len σ₁ = lay P.I.hashLen P.I.ecdsa.curve.len σ₂ := by
  obtain ⟨-, -, hsp, h3, h4, h5, h6, -⟩ := h
  simp only [lay, hsp, h3, h4, h5, h6]

theorem block_two {is : List Instr} {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h : TaintOk [] is) : RelCT isa R (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs []) (fun a b hr => ⟨hsp a b hr, fun r hr => by
    simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) h

theorem save_ct : RelCT isa (Entered P) (.block Cfg.saveArgs) (Two P fun _ _ _ _ _ => True) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := block_two (R := Entered P) (fun a b ⟨σ₁, σ₂, h, ea, eb⟩ => by
      rw [ea, eb]; show σ₁.sp - 48 - BitVec.ofNat 64 (256 + extra P.c.hHigh P.c.wide) =
        σ₂.sp - 48 - BitVec.ofNat 64 (256 + extra P.c.hHigh P.c.wide); rw [h.2.2.1])
    saveArgs_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, h, rfl, rfl⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok (pre_conv h.1)
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok (pre_conv h.2.1)
  rw [← e_eq (lay_q P σ₁)] at x₁
  rw [← e_eq (lay_q P σ₂)] at x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  rw [← lay_eq h] at y₂
  refine ⟨ht, _, _, _, _, _, _, _, lay_ok (pre_conv h.1), lay_q P σ₁, ?_, y₁, y₂, trivial, trivial⟩
  obtain ⟨-, -, h4, h5, -, hr⟩ := h.2.2
  have e : (result P.I σ₁.mem (σ₁.gpr .r4) (σ₁.gpr .r5)).2 = (result P.I σ₂.mem (σ₁.gpr .r4) (σ₁.gpr .r5)).2 := by
    rw [hr, h4, h5]
  simp only [exitAt, show (lay P.I.hashLen P.I.ecdsa.curve.len σ₁).d = σ₁.gpr .r4 from rfl,
    show (lay P.I.hashLen P.I.ecdsa.curve.len σ₁).dg = σ₁.gpr .r5 from rfl, e]

/-- Constant time: only the pointers and the number of candidates RFC 6979
tries affect it. -/
theorem sign_ct (B : Blks P.K P.c) :
    ConstantTime isa (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pre (rfcPPC P.I (400 + extra P.c.hHigh P.c.wide)).pub P.c.sign := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  rw [Cfg.sign]
  refine RelCT.seq (R := fun a b => ∃ σ₁ σ₂, Pre2 P σ₁ σ₂ ∧ a = lrSaved σ₁ ∧ b = lrSaved σ₂) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨ht, -⟩ := block_two (is := [.mflr .r0]) (R := Pre2 P) (fun _ _ h => h.2.2.1) ⟨_, by taint_decide⟩
      _ _ _ _ _ _ hp e₁ e₂
    have w : ∀ s, WP isa (.block [.mflr .r0]) s fun s' => s' = lrSaved s := fun s =>
      Proof.Mont.PPC64LE.wp_step exec_mflr (wp_nil rfl)
    obtain ⟨_, u₁, x₁, y₁⟩ := w s₁
    obtain ⟨_, u₂, x₂, y₂⟩ := w s₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, hp, y₁, y₂⟩
  refine RelCT.seq (RelCT.frame (fun _ _ ⟨σ₁, σ₂, h, ea, eb⟩ => by rw [ea, eb]; exact h.2.2.1)
    (RelCT.alloc (R := fun _ _ => True) (fun _ _ ⟨_, _, ⟨σ₁, σ₂, h, ea, eb⟩, ea', eb'⟩ => by
      rw [ea', eb', ea, eb]; show σ₁.sp - 48 = σ₂.sp - 48; rw [h.2.2.1]) ?_)) ?_
  · refine RelCT.mono (P := Entered P) ?_ (fun a b ⟨_, _, ⟨_, _, ⟨σ₁, σ₂, h, ea, eb⟩, ea', eb'⟩, ea'', eb''⟩ =>
      ⟨σ₁, σ₂, h, by rw [ea'', ea', ea]; rfl, by rw [eb'', eb', eb]; rfl⟩) fun _ _ h => h
    rw [Cfg.body]
    exact save_ct.seq (rest_ct B)
  · exact block_two (fun _ _ h => h) ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
