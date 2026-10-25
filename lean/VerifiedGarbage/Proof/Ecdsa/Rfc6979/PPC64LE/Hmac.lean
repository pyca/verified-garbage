module

import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Layout
public import VerifiedGarbage.Proof.Mont.PPC64LE.Words

/-!
# Deterministic ECDSA on PPC64LE: one HMAC

`HMAC_K(data)` (`Cfg.hmac`), for the key `K` (of the hash function's output
length) at the frame's `K` and `len` bytes of data in the frame or in
`scratch` above HMAC's working space (`DataOk`), written to the frame at
`dst`: HMAC's `init` with `K` (`init_step`), the streaming `update` on the
inner state (`upd_step`), and HMAC's `finalize` (`fin_step`). They change
only HMAC's states and working space (the first 2256 bytes of `scratch`),
the 96 bytes below the frame, and `dst` (`hmac_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The bytes of a region apart from what changed are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  exact Frame.bytes (R := ⟨p, n⟩) hf hd hn hi

theorem Lay.Ok.sp_toNat {L : Lay dn} (hL : L.Ok) : (L.B + BitVec.ofNat 64 96).toNat = L.B.toNat + 96 := by
  have := hL.nB
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith : 96 < 2 ^ 64), Nat.mod_eq_of_lt (by omega_arith)]

theorem Lay.below96 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 96 = ⟨L.B, 96⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 96, 96⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

theorem Lay.below48 (L : Lay dn) : below (L.B + BitVec.ofNat 64 96) 48 = ⟨L.B + BitVec.ofNat 64 48, 48⟩ := by
  show (⟨L.B + BitVec.ofNat 64 96 - BitVec.ofNat 64 48, 48⟩ : Region) = _
  congr 1
  rw [show (BitVec.ofNat 64 96 : BitVec 64) = BitVec.ofNat 64 48 + BitVec.ofNat 64 48 from rfl, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

/-- The key `K`: the first `D` bytes of the frame's `K`. -/
abbrev keyOf (P : Kit) (L : Lay dn) (m : Mem) : List Byte := Spec.Sha256.bytesAt m (L.B + BitVec.ofNat 64 128) P.H.D

/-- The regions of `scratch` HMAC's functions use: the states and the working space. -/
abbrev hmacScr (L : Lay dn) : Region := ⟨L.scr, 2256⟩

theorem scr_sub (L : Lay dn) {e k : Nat} (h : e + k ≤ 2256) : Region.Sub ⟨L.scr + BitVec.ofNat 64 e, k⟩ (hmacScr L) :=
  Offset.sub_base _ h

/-- After HMAC's `init`: its states for the key `K` in the frame on entry `t`. -/
structure Inited (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u.mem
  inner : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad)
  outer : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem init_step (P : Kit) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.seq (.block (Cfg.hmacArgs₁ P.H.D)) (.call P.hm.initN P.hm.initC)) t (Inited P L g lr m₀ t) := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.hS
  have hD := P.hH.hD64
  have hDB := P.hH.hDB
  have hSc := P.hScr
  simp only [sWork, sMsg] at hSc
  refine WP.seq (WP.mono (args₁_ok hL hc (D := P.H.D) (by omega_arith)) fun u ⟨hcu, hmu, _, h3, h4, h5, h6, h7⟩ => ?_)
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have kS : ∀ {e k : Nat}, e + k ≤ 8192 → Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by omega_arith) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine initCall P h3 h4 h5 (by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]) h7
    (by rw [P.hIS, P.hH.hB]; exact hDB)
    (dS (by omega_arith) (by omega_arith) (by omega_arith)) (kS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith))
    (kS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith)) (kS (by omega_arith))
    (by rw [hsp, hL.sp_toNat]; omega_arith) (bS (by omega_arith)) (bS (by omega_arith))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (bS (by omega_arith))
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    (hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    fun u' h₁ h₂ h₃ h₄ hcs hi ho => ?_
  rw [hsp, L.below96] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, P.I.scratch * 8⟩] ++ [⟨L.B, 96⟩], Safe L r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact safe_scr L (by omega_arith)
    · exact safe_scr L (by omega_arith)
    · exact safe_scr L (by omega_arith)
    · exact .inr (.inr (.inl (Region.sub_prefix (by omega_arith))))
  refine ⟨hcu.keep hL h₁ h₂ h₃ hcs h₄ hs, hmu ▸ h₄.sub fun r hr => ?_, ?_, ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨⟨L.B, 96⟩, by simp, fun _ h => h⟩
  · rw [← P.hIS, ← hmu]; exact hi
  · rw [← P.hIS, ← hmu]; exact ho

/-- Where the data may be: in the frame's `K`, `V` and `h`, or in `scratch`
above HMAC's working space. -/
def DataOk (L : Lay dn) (da : Addr) (len : Nat) : Prop :=
  (∃ o, da = L.B + BitVec.ofNat 64 o ∧ 128 ≤ o ∧ o + len ≤ 312) ∨
    (∃ o, da = L.scr + BitVec.ofNat 64 o ∧ 2256 ≤ o ∧ o + len ≤ 8192)

namespace DataOk

variable {da : Addr} {len : Nat}

/-- The data is apart from HMAC's states and working space. -/
theorem scr (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 2256) :
    Region.Disjoint ⟨da, len⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact hL.stk_scr (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The data is apart from the stack below the frame. -/
theorem low (hd : DataOk L da len) (hL : L.Ok) {e k : Nat} (h : e + k ≤ 96) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 e, k⟩ ⟨da, len⟩ := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact Offset.disjoint _ (by omega_arith) (by have := hL.nB; omega_arith) (by omega_arith)
  · exact hL.stk_scr (by omega_arith) (by omega_arith)

theorem within (hd : DataOk L da len) : ∃ R ∈ [L.D, L.DG, L.FR, L.OUT, L.SCR], Within ⟨da, len⟩ R := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩
  · exact ⟨L.FR, by simp, within_fr _ h₁ (by omega_arith)⟩
  · exact ⟨L.SCR, by simp, within_off _ h₂⟩

theorem len_le (hd : DataOk L da len) : len ≤ 8192 := by
  rcases hd with ⟨o, rfl, h₁, h₂⟩ | ⟨o, rfl, h₁, h₂⟩ <;> omega_arith

end DataOk

/-- After the streaming `update`: the inner state holds the data too. -/
structure Updated (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) (da : Addr)
    (len : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩] t.mem u.mem
  inner : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 0)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.ipad ++
      Spec.Sha256.bytesAt t.mem da len)
  outer : P.hH.SH.Repr u.mem (L.scr + BitVec.ofNat 64 192)
    (Spec.Hmac.xorPad (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t.mem)) Spec.Hmac.opad)

theorem blockKey_length (P : Kit) {k : List Byte} (hk : k.length ≤ P.H.B) :
    (Spec.Hmac.blockKey P.hH.SH.H k).length = P.H.B := by
  have hB := P.hH.hB
  simp only [Spec.Hmac.blockKey, hB, show ¬ P.H.B < k.length by omega_arith, ite_false, List.length_append,
    List.length_replicate]
  omega_arith

theorem keyOf_length (P : Kit) (m : Mem) : (keyOf P L m).length = P.H.D := by
  simp [keyOf, Spec.Sha256.bytesAt]

theorem upd_step (P : Kit) (hL : L.Ok) {t₀ t : State} (hI : Inited P L g lr m₀ t₀ t) {dataA : List Instr}
    {da : Addr} {len : Nat} (hd : DataOk L da len) (hlen : len < 2 ^ 15)
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da) :
    WP isa (.seq (.block (Cfg.hmacArgs₂ P.H.B dataA len)) (.call P.hm.updN P.hm.updC)) t
      (Updated P L g lr m₀ t₀ da len) := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.hS
  have hW := P.hW
  simp only [sWork, sMsg] at hW
  have hB : P.H.B < 2 ^ 15 := by rcases P.hH.dims.B with h | h <;> omega_arith
  have hc := hI.ctx
  refine WP.seq (WP.mono (args₂_ok hL hc hB hlen hdA) fun u
    ⟨hcu, hmu, _, h3, h4, h5, h6, h7⟩ => ?_)
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 48).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below48]; exact hL.stk_scr (by omega_arith) h
  have hl := hd.len_le
  refine P.hH.callUpd_ok (st := L.scr + BitVec.ofNat 64 0) (scr := L.scr + BitVec.ofNat 64 384) h3 h5
    (by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]) h7
    (dS (by omega_arith) (by omega_arith) (by omega_arith)) (hd.scr hL (by omega_arith)) (hd.scr hL (by omega_arith))
    (by rw [hsp, hL.sp_toNat]; omega_arith) (bS (by omega_arith))
    (by rw [hsp, L.below48]; exact hd.low hL (by omega_arith)) (bS (by omega_arith))
    (hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.within
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    (hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    fun u' h₁ h₂ h₃ h₄ hcs hupd => ?_
  rw [hsp, L.below48] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 384, P.H.W⟩] ++
      [⟨L.B + BitVec.ofNat 64 48, 48⟩], Safe L r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact safe_scr L (by omega_arith)
    · exact safe_scr L (by omega_arith)
    · exact safe_low L (by omega_arith)
  have hf : Frame [hmacScr L, ⟨L.B, 96⟩] u.mem u'.mem := h₄.sub fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨⟨L.B, 96⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
  -- The data, as on entry.
  have hdata : Spec.Sha256.bytesAt u.mem da len = Spec.Sha256.bytesAt t₀.mem da len := by
    rw [hmu]
    refine bytesAt_frame hI.frame (fun r hr => ?_) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := hd.scr hL (e := 0) (k := 2256) (by omega_arith)
      rwa [BitVec.add_zero] at this
    · have := (hd.low hL (e := 0) (k := 96) (by omega_arith)).symm
      rwa [BitVec.add_zero] at this
  refine ⟨hcu.keep hL h₁ h₂ h₃ hcs h₄ hs, hI.frame.trans (hmu ▸ hf), ?_, ?_⟩
  · rw [← hdata]
    refine hupd _ (hmu ▸ hI.inner) ?_
    rw [h4, Spec.Hmac.xorPad, List.length_map, blockKey_length P (by rw [keyOf_length]; exact P.hH.hDB)]
  · refine P.hH.congr _ _ _ _ (fun i hi => ?_) (hmu ▸ hI.outer)
    refine Frame.bytes (R := ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩) h₄ (fun r hr => ?_)
      (by show P.H.S ≤ 2 ^ 64; omega_arith) hi
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dS (by omega_arith) (by omega_arith) (by omega_arith)
    · exact dS (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (hL.stk_scr (by omega_arith) (by omega_arith)).symm

/-- After HMAC's `finalize`: the MAC at `dst`. -/
structure Macd (P : Kit) (L : Lay dn) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) (da : Addr)
    (len dst : Nat) (u : State) : Prop where
  ctx : Ctx L g lr m₀ u
  frame : Frame [hmacScr L, ⟨L.B, 96⟩, ⟨L.B + BitVec.ofNat 64 (96 + dst), P.H.D⟩] t.mem u.mem
  mac : Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (96 + dst)) P.H.D =
    Spec.Hmac.hmac P.hH.SH.H (keyOf P L t.mem) (Spec.Sha256.bytesAt t.mem da len)

theorem fin_step (P : Kit) (hL : L.Ok) {t₀ t : State} {da : Addr} {len dst : Nat}
    (hU : Updated P L g lr m₀ t₀ da len t) (hlen : P.H.B + len < 2 ^ 15) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216) :
    WP isa (.seq (.block (Cfg.hmacArgs₃ P.H.B len dst)) (.call P.hm.finN P.hm.finC)) t
      (Macd P L g lr m₀ t₀ da len dst) := by
  have hnB := hL.nB
  have hnc := hL.nc
  have hS := P.hS
  have hD := P.hH.hD64
  have hSc := P.hScr
  simp only [sWork, sMsg] at hSc
  have hc := hU.ctx
  refine WP.seq (WP.mono (args₃_ok hL hc hlen (by omega_arith)) fun u ⟨hcu, hmu, _, h3, h4, h5, h6, h7⟩ => ?_)
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega_arith) (by omega_arith)
  have oS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (96 + dst), P.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by omega_arith) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine finCall P (inner := L.scr + BitVec.ofNat 64 0) (outer := L.scr + BitVec.ofNat 64 192)
    (out := L.B + BitVec.ofNat 64 (96 + dst)) (scr := L.scr + BitVec.ofNat 64 384) h3 h4 h6 h7
    (dS (by omega_arith) (by omega_arith) (by omega_arith)) (oS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith))
    (oS (by omega_arith)).symm (dS (by omega_arith) (by omega_arith) (by omega_arith)) (oS (by omega_arith))
    (by rw [hsp, hL.sp_toNat]; omega_arith) (bS (by omega_arith)) (bS (by omega_arith))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (bS (by omega_arith))
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (by rw [Offset.toNat_add_ofNat]; omega_arith) (by rw [Offset.toNat_add_ofNat]; omega_arith)
    (hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    (hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by omega_arith)⟩)
    fun u' h₁ h₂ h₃ h₄ hcs hfin => ?_
  rw [hsp, L.below96] at h₄
  have hs : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.B + BitVec.ofNat 64 (96 + dst), P.H.D⟩,
      ⟨L.scr + BitVec.ofNat 64 384, P.I.scratch * 8⟩] ++ [⟨L.B, 96⟩], Safe L r := by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact safe_scr L (by omega_arith)
    · exact safe_low L (by omega_arith)
    · exact safe_scr L (by omega_arith)
    · exact .inr (.inr (.inl (Region.sub_prefix (by omega_arith))))
  have hk := keyOf_length P (L := L) t₀.mem
  have hbk := blockKey_length P (k := keyOf P L t₀.mem) (by rw [hk]; exact P.hH.hDB)
  have hbs : P.I.S.H.blockSize = P.H.B := by rw [P.hIS]; exact P.hH.hB
  have htl : (Spec.Sha256.bytesAt t₀.mem da len).length = len := by simp [Spec.Sha256.bytesAt]
  refine ⟨hcu.keep hL h₁ h₂ h₃ hcs h₄ hs, (hU.frame.mono (by simp)).trans (hmu ▸ h₄.sub fun r hr => ?_), ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨hmacScr L, by simp, scr_sub L (by omega_arith)⟩
    · exact ⟨⟨L.B, 96⟩, by simp, fun _ h => h⟩
  · have := hfin (Spec.Hmac.blockKey P.hH.SH.H (keyOf P L t₀.mem)) (Spec.Sha256.bytesAt t₀.mem da len)
      (by rw [hbk, hbs]) (by rw [hbk, htl]; omega_arith) (by rw [P.hIS, hmu]; exact hU.inner)
      (by rw [h5, hbs, htl]) (by rw [P.hIS, hmu]; exact hU.outer)
    rw [this, P.hIS]; rfl

/-- `HMAC_K(data)` into the frame at `dst`. -/
theorem hmac_ok (P : Kit) {c : Cfg} (hcH : c.H = P.hm) (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t)
    {dataA : List Instr} {da : Addr} {len dst : Nat} (hd : DataOk L da len) (hlen : P.H.B + len < 2 ^ 15)
    (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
    (hdA : ∀ u, Ctx L g lr m₀ u → u.gpr .r12 = L.scr → WP isa (.block dataA) u fun u' =>
      Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da) :
    WP isa (c.hmac dataA len dst) t (Macd P L g lr m₀ t da len dst) := by
  rw [Cfg.hmac, hcH]
  refine WP.seq (WP.mono (WP.seq_iff.mp (init_step P hL hc)) fun u hu => WP.seq (WP.mono hu fun u₁ hI => ?_))
  refine WP.seq (WP.mono (WP.seq_iff.mp (upd_step P hL hI hd (by omega_arith) hdA)) fun u hu =>
    WP.seq (WP.mono hu fun u₂ hU => ?_))
  exact fin_step P hL hU hlen hdst

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
