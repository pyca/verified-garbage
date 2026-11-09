module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Hash
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Deterministic ECDSA on PPC64LE: HMAC through the table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Hmac.lean`): the table's
functions, each called indirectly (`tcall_ok`: the table's word, which
`Ctx` says holds the function of `L.w`, whose call an indirect call of
`L.f`'s functions reaches), with the lengths and counts the frame's `D` and
`B` give:

* HMAC's `init` with the key `K` (`D` bytes, the frame's first): HMAC's states
  for the block key `K₀` of `K` (`init_step`);
* the streaming `update` of the inner state with `len` bytes of data in the
  frame below its pointers or in `scratch` above HMAC's working space
  (`DataOk`), the inner state holding `K₀ ⊕ ipad ‖ text`, of `B + |text|`
  bytes: it then holds the data after `text` (`upd_call_ok`), with `V`
  (`updV_step`) or with the message at `scratch + sMsg` (`updM_step`);
* HMAC's `finalize`, with the count `B + D + len` for a text of that length,
  writing `HMAC(K₀, text)` (`D` bytes) to the frame at `dst` (`fin_step`).

`St P L g lr m₀ k0 text` is what holds between them: `Ctx`, and HMAC's states
for `K₀` with the inner one holding `text`. They change only HMAC's states
and working space (the first 2256 bytes of `scratch`), the 96 bytes below
the frame, and `dst` (`W`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

theorem _root_.VG.Proof.Mont.PPC64LE.Kp.toA {rs : List Reg} {s s' : State} (k : Kp rs s s')
    (h : ∀ r ∈ rs, r ∈ [Reg.r3, .r4, .r5, .r6, .r7, .r11, .r12] := by decide) :
    Kp [.r3, .r4, .r5, .r6, .r7, .r11, .r12] s s' := k.mono h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem Lay.below96 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 96 = ⟨L.B, 96⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 96, 96⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

theorem Lay.below48 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 48 = ⟨L.B + BitVec.ofNat 64 48, 48⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 48, 48⟩ : Region) = _
  congr 1
  rw [show (BitVec.ofNat 64 96 : BitVec 64) = BitVec.ofNat 64 48 + BitVec.ofNat 64 48 from rfl, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

theorem Lay.Ok.sp_toNat (hL : L.Ok) : (L.B + BitVec.ofNat 64 96).toNat = L.B.toNat + 96 := by
  have := hL.nB
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega : 96 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- The bytes of a region apart from what changed are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  exact Frame.bytes (R := ⟨p, n⟩) hf hd hn hi

/-- Where the data may be: in the frame below its pointers, or in `scratch`
above HMAC's working space. -/
def DataOk (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 128 ≤ o ∧ o + len ≤ 272) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

namespace DataOk

variable {da : Addr} {len : Nat}

/-- The data is apart from HMAC's states and working space. -/
theorem scr (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)

/-- The data is apart from the stack below the frame. -/
theorem low (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 96) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 e, k⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.disjoint _ (by omega) (by have := hL.nB; omega) (by omega)
  · exact hL.stk_scr (by omega) (by omega)

theorem within (hd : DataOk L da len) : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

theorem len_le (hd : DataOk L da len) : len ≤ 8192 := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩ <;> omega

end DataOk

/-! ## Loads from the frame -/

/-- Through `Kp`, the permissions are `Ctx`'s. -/
theorem Ctx.inFrK {t : State} (hc : Ctx L g lr m₀ t) {rs : List Reg} {t' : State} (k : Kp rs t t') {d n : Nat}
    (h₁ : 128 ≤ d) (h₂ : d + n ≤ 688) : InRegions (t'.rd ++ t'.wr) (L.B + BitVec.ofNat 64 d) n := by
  rw [k.rd, k.wr]; exact hc.inFr h₁ h₂

/-- The frame's base in `r11` and `scratch` in `r12`. -/
theorem scrBase_ok {t : State} (hc : Ctx L g lr m₀ t) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Kp [.r11, .r12] t t' → t'.mem = t.mem → t'.gpr .r11 = L.B + BitVec.ofNat 64 96 →
      t'.gpr .r12 = L.scr → WP isa (.block is) t' Q) :
    WP isa (.block (Cfg.scrBase ++ is)) t Q := by
  simp only [Cfg.scrBase, List.cons_append, List.nil_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine k t₂ (k₁.mono.trans k₂.mono) (by rw [m₂, m₁]) (by rw [k₂.gpr _ (by decide), hb]) ?_
  rw [v₂, m₁, hc.pScr]

/-- `scratch` in `r3`, the frame in `r11`. -/
theorem argBase_ok {t : State} (hc : Ctx L g lr m₀ t) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Kp [.r11, .r3] t t' → t'.mem = t.mem → t'.gpr .r11 = L.B + BitVec.ofNat 64 96 →
      t'.gpr .r3 = L.scr → WP isa (.block is) t' Q) :
    WP isa (.block (Cfg.argBase ++ is)) t Q := by
  simp only [Cfg.argBase, List.cons_append, List.nil_append]
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  refine k t₂ (k₁.mono.trans k₂.mono) (by rw [m₂, m₁]) (by rw [k₂.gpr _ (by decide), hb]) ?_
  rw [v₂, m₁, hc.pScr]

/-- The table is of `P`'s hash function and functions. -/
def TabL (P : RfcHash) (L : Lay dn) : Prop := L.w = P.v ∧ L.f = P.f

/-- The frame's `D`. -/
theorem Ctx.dl (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 304) 64 = BitVec.ofNat 64 P.v.H.D := by
  rw [← hT.1]; exact hc.pDl

/-- The frame's `B`. -/
theorem Ctx.bl (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    t.mem.readW (L.B + BitVec.ofNat 64 312) 64 = BitVec.ofNat 64 P.v.H.B := by
  rw [← hT.1]; exact hc.pBl

/-- The registers the argument blocks write. -/
abbrev argRegs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r11, .r12]


/-! ## The table -/

/-- The indirect call of the table's function `j`, at the address its word
`j` holds, of `n`. -/
theorem tcall_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) (h11 : t.gpr .r11 = L.B + BitVec.ofNat 64 96)
    {j : Nat} (hj : 8 * j + 8 ≤ 48)
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)}
    (hw : m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n)
    (hf : ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c)) {Q : State → Prop}
    (h : ∀ t', Ctx L g lr m₀ t' → t'.mem = t.mem → (∀ r, r ≠ .r12 → t'.gpr r = t.gpr r) →
      WP isa (.call n c) t' Q) :
    WP isa (Cfg.tcall j ts) t Q := by
  unfold Cfg.tcall
  refine WP.seq (WP.of_syms (stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide)
    (by rw [h11, fr_add]; rfl) (hc.inFrK (Kp.refl [] t) (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_))
  have h12 : t₂.gpr .r12 = L.tab := by rw [v₂, hc.pTab]
  refine stepLd (a := L.tab + BitVec.ofNat 64 (8 * j)) (by decide) ⟨by omega, by omega⟩ (by rw [h12])
    (by rw [k₂.rd, k₂.wr]; exact hc.inTab hL hj) fun t₃ k₃ m₃ v₃ => wp_nil fun hsy => ?_
  have K : Kp [.r12] t t₃ := k₂.trans k₃
  have hm : t₃.mem = t.mem := by rw [m₃, m₂]
  have hc₃ : Ctx L g lr m₀ t₃ := hc.kp hL K hm hsy
  have h12' : t₃.gpr .r12 = t.syms n := by rw [v₃, m₂, hc.tabWord hL hj, hw]
  refine WP.icalls_of_call (a := t.syms n) (by simp only [PPC64LE.icall, h12']) ?_
    (h t₃ hc₃ hm fun r hr => K.gpr r (by simp [hr]))
  show ts.find? (fun q => t₃.syms q.1 == t.syms n) = _
  rw [hsy]; exact hf

/-! ## HMAC's states -/

/-- The key `K`: the first `D` bytes of the frame's `K`. -/
abbrev keyOf (P : RfcHash) (L : Lay dn) (m : Mem) : List Byte :=
  Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 128) P.v.H.D

/-- HMAC's states for the block key `k0`, the inner one holding `text`
after `K₀ ⊕ ipad`. -/
structure St (P : RfcHash) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (k0 text : List Byte)
    (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  klen : k0.length = P.v.H.B
  tlen : text.length ≤ 512
  inner : P.v.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0) (Spec.Hmac.xorPad k0 Spec.Hmac.ipad ++ text)
  outer : P.v.ok.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192) (Spec.Hmac.xorPad k0 Spec.Hmac.opad)

/-- What HMAC's functions write: their states and working space, and the
stack below the frame. -/
abbrev W (L : Lay dn) : List Region := [⟨L.scr, 2256⟩, ⟨L.B, 96⟩]

theorem scr_work {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr, 2256⟩ :=
  Offset.sub_base _ h

theorem xorPad_length (k : List Byte) (p : Byte) : (Spec.Hmac.xorPad k p).length = k.length :=
  List.length_map _

theorem blockKey_length {k : List Byte} (hk : k.length = P.v.H.D) :
    (Spec.Hmac.blockKey P.v.ok.SH.H k).length = P.v.H.B := by
  have hB := P.v.ok.hB
  have hDB : P.v.H.D < P.v.H.B := by nums
  simp only [Spec.Hmac.blockKey, hk, hB, show ¬ P.v.H.B < P.v.H.D by omega, ite_false, List.length_append,
    List.length_replicate]
  omega

theorem keyOf_length (m : Mem) : (keyOf P L m).length = P.v.H.D := by simp [keyOf, Spec.Sha256.bytesAt]

/-! ## HMAC's `init` -/

/-- The arguments of HMAC's `init`. -/
theorem initArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.initArgs) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp argRegs t t' ∧
      t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .r5 = L.B + BitVec.ofNat 64 128 ∧ t'.gpr .r6 = BitVec.ofNat 64 P.v.H.D ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 ∧
      t'.gpr .r11 = L.B + BitVec.ofNat 64 96 := by
  refine WP.of_syms (argBase_ok hc fun t₁ k₁ m₁ b₁ s₁ => ?_)
  refine stepAddi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddSp (by decide) fun t₄ k₄ m₄ v₄ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁, fr_add]; rfl)
    (hc.inFrK ((k₁.toA.trans k₃.toA).trans k₄.toA) (by omega) (by omega))
    fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil fun hsy => ?_
  have K : Kp argRegs t t₆ := ((((k₁.toA.trans k₃.toA).trans k₄.toA).trans k₅.toA).trans k₆.toA)
  have hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₁]
  refine ⟨hc.kp hL K hm hsy, hm, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]
    exact (BitVec.add_zero _).symm
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄, k₃.sp, k₁.sp, hc.sp, fr_add]; rfl
  · rw [k₆.gpr _ (by decide), v₅, m₄, m₃, m₁]; exact hc.dl hT
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]

/-- HMAC's `init` with the key `K` in the frame: HMAC's states for its block key. -/
theorem init_step (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (cfgOf P).initK t fun u => St P L g lr m₀ (Spec.Hmac.blockKey P.v.ok.SH.H (keyOf P L t.mem)) [] u ∧
      Frame (W L) t.mem u.mem := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.K.hS
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  refine WP.seq (WP.mono (initArgs_ok hL hT hc) fun u ⟨hcu, hmu, _, h3, h4, h5, h6, h7, h11⟩ => ?_)
  have hok := hcu.tabOk
  have htm := hcu.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcu h11 (j := 0) (by decide) htm.1 hok.i fun u' hc' hm' hk' => ?_
  have hsp : u'.sp = L.B + BitVec.ofNat 64 96 := hc'.sp
  have e : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], u'.gpr r = u.gpr r := fun r hr => hk' r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have kS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, P.v.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by nums) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u'.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  have hDB : P.v.H.D ≤ P.v.H.B := by nums
  refine WP.of_syms (initCall P.K (n := P.v.initN) (inner := L.scr + BitVec.ofNat 64 0)
    (outer := L.scr + BitVec.ofNat 64 192) (key := L.B + BitVec.ofNat 64 128)
    (scr := L.scr + BitVec.ofNat 64 384) (kl := P.v.H.D)
    ((e _ (by simp)).trans h3) ((e _ (by simp)).trans h4) ((e _ (by simp)).trans h5)
    (by rw [(e _ (by simp)).trans h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by nums)]) ((e _ (by simp)).trans h7)
    (by show P.v.H.D ≤ P.v.I.S.H.blockSize; rw [P.v.hIS, P.v.ok.hB]; exact hDB)
    (dS (by nums) (by nums) (by nums)) (kS (by nums)).symm (dS (by nums) (by nums) (by nums))
    (kS (by nums)).symm (dS (by nums) (by nums) (by nums)) (kS (by nums))
    (by rw [hsp, hL.sp_toNat]; omega) (bS (by nums)) (bS (by nums))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega) (by nums)) (bS (by nums))
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (hc'.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      all_goals exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    (hc'.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    fun u'' h₁ h₂ h₃ h₄ hcs hi ho hsy => ?_)
  rw [hsp, L.below96] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.K.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩] ++ [⟨L.B, 96⟩], Region.Sub r ⟨L.scr, 2256⟩ ∨
        Region.Sub r ⟨L.B, 96⟩ := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact .inl (scr_work (by nums))
    · exact .inl (scr_work (by nums))
    · exact .inl (scr_work (by nums))
    · exact .inr fun _ h => h
  have hkey : keyOf P L u'.mem = keyOf P L t.mem := by simp only [keyOf, hm', hmu]
  refine ⟨⟨hc'.keep hL h₁ h₂ h₃ hcs h₄ (fun r hr => by
      rcases hs r hr with h | h
      · exact .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))
      · exact .inr (.inr (.inl (sub_trans h (Region.sub_prefix (by omega)))))) hsy,
    blockKey_length (keyOf_length _), by simp, ?_, ?_⟩, ?_⟩
  · rw [List.append_nil, ← P.v.hIS, ← hkey]; exact hi
  · rw [← P.v.hIS, ← hkey]; exact ho
  · rw [← hmu, ← hm']
    exact h₄.sub fun r hr => by
      rcases hs r hr with h | h
      · exact ⟨⟨L.scr, 2256⟩, by simp, h⟩
      · exact ⟨⟨L.B, 96⟩, by simp, h⟩

/-! ## The streaming `update` -/

/-- The arguments of the streaming `update` with `V`. -/
theorem updVArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.updVArgs) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp argRegs t t' ∧
      t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = BitVec.ofNat 64 P.v.H.B ∧
      t'.gpr .r5 = L.B + BitVec.ofNat 64 192 ∧ t'.gpr .r6 = BitVec.ofNat 64 P.v.H.D ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 ∧
      t'.gpr .r11 = L.B + BitVec.ofNat 64 96 := by
  refine WP.of_syms (argBase_ok hc fun t₁ k₁ m₁ b₁ s₁ => ?_)
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide)
    (by rw [b₁, fr_add]; rfl) (hc.inFrK k₁.toA (by omega) (by omega)) fun t₃ k₃ m₃ v₃ => ?_
  refine stepAddSp (by decide) fun t₄ k₄ m₄ v₄ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁, fr_add]; rfl)
    (hc.inFrK ((k₁.toA.trans k₃.toA).trans k₄.toA) (by omega) (by omega))
    fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => wp_nil fun hsy => ?_
  have K : Kp argRegs t t₆ := ((((k₁.toA.trans k₃.toA).trans k₄.toA).trans k₅.toA).trans k₆.toA)
  have hm : t₆.mem = t.mem := by rw [m₆, m₅, m₄, m₃, m₁]
  refine ⟨hc.kp hL K hm hsy, hm, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]
    exact (BitVec.add_zero _).symm
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, m₁]; exact hc.bl hT
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), v₄, k₃.sp, k₁.sp, hc.sp, fr_add]; rfl
  · rw [k₆.gpr _ (by decide), v₅, m₄, m₃, m₁]; exact hc.dl hT
  · rw [v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]; rfl
  · rw [k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]

/-- The arguments of the streaming `update` with the message's `len` bytes. -/
theorem updMArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) {len : Nat}
    (hlen : len < 2 ^ 15) :
    WP isa (.block (Cfg.updMArgs len)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp argRegs t t' ∧
      t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = BitVec.ofNat 64 (P.v.H.B + P.v.H.D) ∧
      t'.gpr .r5 = L.scr + BitVec.ofNat 64 sMsg ∧ t'.gpr .r6 = BitVec.ofNat 64 len ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 ∧
      t'.gpr .r11 = L.B + BitVec.ofNat 64 96 := by
  refine WP.of_syms (argBase_ok hc fun t₁ k₁ m₁ b₁ s₁ => ?_)
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide)
    (by rw [b₁, fr_add]; rfl) (hc.inFrK k₁.toA (by omega) (by omega)) fun t₃ k₃ m₃ v₃ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), b₁, fr_add]; rfl)
    (hc.inFrK (k₁.toA.trans k₃.toA) (by omega) (by omega)) fun t₄ k₄ m₄ v₄ => ?_
  refine stepAdd fun t₅ k₅ m₅ v₅ => ?_
  refine stepAddi (by decide) (by decide) fun t₆ k₆ m₆ v₆ => ?_
  refine stepLi hlen fun t₇ k₇ m₇ v₇ => ?_
  refine stepAddi (by decide) (by decide) fun t₈ k₈ m₈ v₈ => wp_nil fun hsy => ?_
  have K : Kp argRegs t t₈ :=
    ((((((k₁.toA.trans k₃.toA).trans k₄.toA).trans k₅.toA).trans k₆.toA).trans k₇.toA).trans k₈.toA)
  have hm : t₈.mem = t.mem := by rw [m₈, m₇, m₆, m₅, m₄, m₃, m₁]
  refine ⟨hc.kp hL K hm hsy, hm, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
      k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]
    exact (BitVec.add_zero _).symm
  · rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), v₅, k₄.gpr _ (by decide), v₃, v₄, m₃,
      m₁, hc.bl hT, hc.dl hT, BitVec.ofNat_add_ofNat]
  · rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), v₆, k₅.gpr _ (by decide), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), s₁]
  · rw [k₈.gpr _ (by decide), v₇]
  · rw [v₈, k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide), k₄.gpr _ (by decide),
      k₃.gpr _ (by decide), s₁]; rfl
  · rw [k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
      k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]

/-- The table's `update` of the inner state, holding `text`, with the data. -/
theorem upd_call_ok (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g lr m₀ k0 text u)
    {da : Addr} {len : Nat} (hd : DataOk L da len) (hlen : len ≤ 256) (htl : text.length + len ≤ 512)
    (h3 : u.gpr .r3 = L.scr + BitVec.ofNat 64 0) (h4 : u.gpr .r4 = BitVec.ofNat 64 (P.v.H.B + text.length))
    (h5 : u.gpr .r5 = da) (h6 : u.gpr .r6 = BitVec.ofNat 64 len) (h7 : u.gpr .r7 = L.scr + BitVec.ofNat 64 384)
    (h11 : u.gpr .r11 = L.B + BitVec.ofNat 64 96) :
    WP isa (Cfg.tcall 1 P.f.upd) u fun u' => St P L g lr m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem da len) u' ∧
      Frame (W L) u.mem u'.mem := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hc := hu.ctx
  have hok := hc.tabOk
  have htm := hc.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hc h11 (j := 1) (by decide) htm.2.1 hok.u fun w hcw hmw hkw => ?_
  have e : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], w.gpr r = u.gpr r := fun r hr => hkw r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsp : w.sp = L.B + BitVec.ofNat 64 96 := hcw.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below w.sp 48).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below48]; exact hL.stk_scr (by omega) h
  have hl := hd.len_le
  have hW := P.K.hW
  simp only [sWork, sMsg] at hW
  refine WP.of_syms (P.v.ok.callUpd_ok (st := L.scr + BitVec.ofNat 64 0) (scr := L.scr + BitVec.ofNat 64 384)
    ((e _ (by simp)).trans h3) ((e _ (by simp)).trans h5)
    (by rw [(e _ (by simp)).trans h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]) ((e _ (by simp)).trans h7)
    (dS (by nums) (by nums) (by nums)) (hd.scr hL (by nums)) (hd.scr hL (by nums))
    (by rw [hsp, hL.sp_toNat]; omega) (bS (by nums))
    (by rw [hsp, L.below48]; exact hd.low hL (by omega)) (bS (by nums))
    (hcw.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.within
      all_goals exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    (hcw.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    fun w' h₁ h₂ h₃ h₄ hcs hupd hsy => ?_)
  rw [hsp, L.below48] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.v.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 384, P.v.H.W⟩] ++
      [⟨L.B + BitVec.ofNat 64 48, 48⟩], Region.Sub r ⟨L.scr, 2256⟩ ∨ Region.Sub r ⟨L.B, 96⟩ := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (scr_work (by nums))
    · exact .inl (scr_work (by nums))
    · exact .inr (Offset.sub_base _ (by omega))
  have hf : Frame (W L) w.mem w'.mem := h₄.sub fun r hr => by
    rcases hs r hr with h | h
    · exact ⟨⟨L.scr, 2256⟩, by simp, h⟩
    · exact ⟨⟨L.B, 96⟩, by simp, h⟩
  have hkl := hu.klen
  refine ⟨⟨hcw.keep hL h₁ h₂ h₃ hcs h₄ (fun r hr => by
      rcases hs r hr with h | h
      · exact .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))
      · exact .inr (.inr (.inl (sub_trans h (Region.sub_prefix (by omega)))))) hsy,
    hkl, by simp [Spec.Sha256.bytesAt]; omega, ?_, ?_⟩, hmw ▸ hf⟩
  · rw [← hmw, ← List.append_assoc]
    refine hupd _ (hmw ▸ hu.inner) ?_
    rw [(e _ (by simp)).trans h4, List.length_append, xorPad_length, hkl]
  · refine P.v.ok.congr _ _ _ _ (fun i hi => ?_) (hmw ▸ hu.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.v.H.S⟩) h₄ (fun r hr => ?_)
      (by show P.v.H.S ≤ 2 ^ 64; nums) hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS (by nums) (by nums) (by nums)
    · exact dS (by nums) (by nums) (by nums)
    · exact (hL.stk_scr (by omega) (by nums)).symm

/-- The inner state, for the key `K₀`, updated with `V`. -/
theorem updV_step (hL : L.Ok) (hT : TabL P L) {k0 : List Byte} {u : State} (hu : St P L g lr m₀ k0 [] u) :
    WP isa (cfgOf P).updV u fun u' =>
      St P L g lr m₀ k0 (Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 192) P.v.H.D) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updVArgs_ok hL hT hu.ctx) fun w ⟨hcw, hmw, _, h3, h4, h5, h6, h7, h11⟩ => ?_)
  have hw : St P L g lr m₀ k0 [] w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := P.v.H.D)
    (.inl ⟨192, rfl, by omega, by nums⟩) (by nums) (by simp; nums) h3 (by simpa using h4) h5 h6 h7 h11)
    fun u' ⟨hs, hf⟩ => ?_
  rw [List.nil_append, hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-- The inner state, for the key `K₀`, holding `text`, updated with the message's `len` bytes. -/
theorem updM_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State}
    (hu : St P L g lr m₀ k0 text u) (ht : text.length = P.v.H.D) {len : Nat} (hlen : len ≤ 256) :
    WP isa ((cfgOf P).updM len) u fun u' =>
      St P L g lr m₀ k0 (text ++ Spec.Sha256.bytesAt u.mem (L.scr + BitVec.ofNat 64 sMsg) len) u' ∧
      Frame (W L) u.mem u'.mem := by
  refine WP.seq (WP.mono (updMArgs_ok hL hT hu.ctx (len := len) (by omega))
    fun w ⟨hcw, hmw, _, h3, h4, h5, h6, h7, h11⟩ => ?_)
  have hw : St P L g lr m₀ k0 text w := ⟨hcw, hu.klen, hu.tlen, hmw ▸ hu.inner, hmw ▸ hu.outer⟩
  refine WP.mono (upd_call_ok hL hT hw (len := len) (.inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega⟩)
    hlen (by rw [ht]; nums) h3 (by rw [h4, ht]) h5 h6 h7 h11) fun u' ⟨hs, hf⟩ => ?_
  rw [hmw] at hs
  exact ⟨hs, hmw ▸ hf⟩

/-! ## HMAC's `finalize` -/

theorem finArgs_ok (hL : L.Ok) (hT : TabL P L) {t : State} (hc : Ctx L g lr m₀ t) {len dst : Nat}
    (hlen : len < 2 ^ 15) (hdst : dst < 2 ^ 15) :
    WP isa (.block (Cfg.finArgs len dst)) t fun t' => Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ Kp argRegs t t' ∧
      t'.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ t'.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
      t'.gpr .r5 = BitVec.ofNat 64 (P.v.H.B + P.v.H.D + len) ∧ t'.gpr .r6 = L.B + BitVec.ofNat 64 (96 + dst) ∧
      t'.gpr .r7 = L.scr + BitVec.ofNat 64 384 ∧
      t'.gpr .r11 = L.B + BitVec.ofNat 64 96 := by
  refine WP.of_syms (argBase_ok hc fun t₁ k₁ m₁ b₁ s₁ => ?_)
  refine stepAddi (by decide) (by decide) fun t₃ k₃ m₃ v₃ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 312) (by decide) (by decide)
    (by rw [k₃.gpr _ (by decide), b₁, fr_add]; rfl)
    (hc.inFrK (k₁.toA.trans k₃.toA) (by omega) (by omega)) fun t₄ k₄ m₄ v₄ => ?_
  refine stepLd (a := L.B + BitVec.ofNat 64 304) (by decide) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁, fr_add]; rfl)
    (hc.inFrK ((k₁.toA.trans k₃.toA).trans k₄.toA) (by omega) (by omega))
    fun t₅ k₅ m₅ v₅ => ?_
  refine stepAdd fun t₆ k₆ m₆ v₆ => ?_
  refine stepAddi (by decide) hlen fun t₇ k₇ m₇ v₇ => ?_
  refine stepAddSp hdst fun t₈ k₈ m₈ v₈ => ?_
  refine stepAddi (by decide) (by decide) fun t₉ k₉ m₉ v₉ => wp_nil fun hsy => ?_
  have K : Kp argRegs t t₉ :=
    (((((((k₁.toA.trans k₃.toA).trans k₄.toA).trans k₅.toA).trans k₆.toA).trans k₇.toA).trans
      k₈.toA).trans k₉.toA)
  have hm : t₉.mem = t.mem := by rw [m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₁]
  refine ⟨hc.kp hL K hm hsy, hm, K, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]
    exact (BitVec.add_zero _).symm
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), v₃, s₁]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), v₇, v₆, k₅.gpr _ (by decide), v₄, v₅, m₄, m₃, m₁,
      hc.bl hT, hc.dl hT, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  · rw [k₉.gpr _ (by decide), v₈, k₇.sp, k₆.sp, k₅.sp, k₄.sp, k₃.sp, k₁.sp, hc.sp, fr_add]
  · rw [v₉, k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
      k₄.gpr _ (by decide), k₃.gpr _ (by decide), s₁]; rfl
  · rw [k₉.gpr _ (by decide), k₈.gpr _ (by decide), k₇.gpr _ (by decide), k₆.gpr _ (by decide),
      k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), b₁]

/-- HMAC's `finalize`, for the key `K₀` and the text `text`, of `D + len`
bytes: the MAC in the frame at `dst`. -/
theorem fin_step (hL : L.Ok) (hT : TabL P L) {k0 text : List Byte} {u : State} (hu : St P L g lr m₀ k0 text u)
    {len dst : Nat} (ht : text.length = P.v.H.D + len) (hlen : len < 2 ^ 14) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 176) :
    WP isa ((cfgOf P).fin len dst) u fun u' => Ctx L g lr m₀ u' ∧
      Frame (W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩]) u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (L.B + BitVec.ofNat 64 (96 + dst)) P.v.H.D =
        Spec.Hmac.hmacBlockKey P.v.ok.SH.H k0 text := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hSc := P.K.hScr
  have hS := P.K.hS
  have eS : P.K.H.S = P.v.H.S := rfl
  have eD : P.K.H.D = P.v.H.D := rfl
  simp only [sWork, sMsg] at hSc
  refine WP.seq (WP.mono (finArgs_ok hL hT hu.ctx (len := len) (dst := dst) (by omega) (by omega))
    fun w ⟨hcw, hmw, _, h3, h4, h5, h6, h7, h11⟩ => ?_)
  have hok := hcw.tabOk
  have htm := hcw.tabMem
  rw [hT.1, hT.2] at hok
  rw [hT.1] at htm
  refine tcall_ok hL hcw h11 (j := 2) (by decide) htm.2.2 hok.f fun w₁ hc₁ hm₁ hk₁ => ?_
  have e : ∀ r ∈ [Reg.r3, .r4, .r5, .r6, .r7], w₁.gpr r = w.gpr r := fun r hr => hk₁ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
  have hsp : w₁.sp = L.B + BitVec.ofNat 64 96 := hc₁.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have oS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by nums) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below w₁.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine WP.of_syms (finCall P.K (n := P.v.finN) (inner := L.scr + BitVec.ofNat 64 0)
    (outer := L.scr + BitVec.ofNat 64 192) (out := L.B + BitVec.ofNat 64 (96 + dst))
    (scr := L.scr + BitVec.ofNat 64 384) ((e _ (by simp)).trans h3) ((e _ (by simp)).trans h4)
    ((e _ (by simp)).trans h6) ((e _ (by simp)).trans h7)
    (dS (by nums) (by nums) (by nums)) (oS (by nums)).symm (dS (by nums) (by nums) (by nums))
    (oS (by nums)).symm (dS (by nums) (by nums) (by nums)) (oS (by nums))
    (by rw [hsp, hL.sp_toNat]; omega) (bS (by nums)) (bS (by nums))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega) (by nums)) (bS (by nums))
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (hc₁.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    (hc₁.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩)
    fun w' h₁ h₂ h₃ h₄ hcs hfin hsy => ?_)
  rw [hsp, L.below96] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩ : Region), ⟨L.B + BitVec.ofNat 64 (96 + dst), P.K.H.D⟩,
      ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩] ++ [⟨L.B, 96⟩],
      ∃ r' ∈ W L ++ [⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩], Region.Sub r r' := by
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩, by simp, fun _ h => h⟩
    · exact ⟨⟨L.scr, 2256⟩, by simp, scr_work (by nums)⟩
    · exact ⟨⟨L.B, 96⟩, by simp, fun _ h => h⟩
  have hm : w₁.mem = u.mem := hm₁.trans hmw
  have hbs : P.v.I.S.H.blockSize = P.v.H.B := by rw [P.v.hIS]; exact P.v.ok.hB
  refine ⟨hc₁.keep hL h₁ h₂ h₃ hcs h₄ (fun r hr => ?_) hsy, hm ▸ h₄.sub hs, ?_⟩
  · obtain ⟨r', hr', hs'⟩ := hs r hr
    simp only [W, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact .inr (.inl (sub_trans hs' (Region.sub_prefix (by omega))))
    · exact .inr (.inr (.inl (sub_trans hs' (Region.sub_prefix (by omega)))))
    · exact (safe_low L (by nums)).of_sub hs'
  · have hk := hu.klen
    have := hfin k0 text (hk.trans hbs.symm) (by rw [hk]; have := hu.tlen; nums)
      (by show P.v.I.S.Repr _ _ _; rw [P.v.hIS, hm]; exact hu.inner)
      (by show _ = BitVec.ofNat 64 (P.v.I.S.H.blockSize + _); rw [(e _ (by simp)).trans h5, hbs, ht, Nat.add_assoc])
      (by show P.v.I.S.Repr _ _ _; rw [P.v.hIS, hm]; exact hu.outer)
    show _ = _
    refine this.trans ?_
    show Spec.Hmac.hmacBlockKey P.v.I.S.H k0 text = _
    rw [P.v.hIS]

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
