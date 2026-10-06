import VerifiedGarbage.Proof.RsaPss.AArch64.Mgf

/-!
# RSASSA-PSS on AArch64: the pieces of the encoding

What each block of `signEnc` does to our working space and the frame:
`DB`'s registers (`dbRegs_ok`), `Y` cleared (`clearY_ok`), `mHash` and the
salt into `Y` (`copyDigest_ok`, `copySaltY_ok`), the length of `M'`
(`signLen_ok`), `EM` cleared (`clearEm_ok`), `0x01` and the salt
(`putSalt_ok`), `H` and `0xbc` (`putH_ok`), and the top bits of `DB`
cleared (`clearTop_ok`).
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_addImm wp_subImm wp_lsr wp_ldrb wp_strb wp_strx
  wp_add wp_sub wp_and eval_zero)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_addSp wp_mov setWidth_ofNat16 copy_ok fill_ok)
open VG.Proof.RsaPss.AArch64.LenLoop (lsr_val)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- A slot of the frame, read. -/
theorem ld_slot {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 d) 8 := by
  rw [L.sp]; exact L.fld hd

theorem updL_nil (V : Nat → Byte) (o : Nat) : updL V o [] = V := by
  funext x; simp only [updL, List.length_nil]; rw [ite_eq_right (by omega)]

/-- `copyLoop` from `n` readable bytes at `q`, apart from our working space,
to `scratch + o`. -/
theorem copyIn_ok {s : State} {F S : Addr} (L : Lay s F S) {V : Nat → Byte} (R : Rep s.mem S V) {q : Addr}
    {o n : Nat} (hn : 0 < n) (ho : o + n ≤ oRsa) (h14 : s.gpr .x14 = off S o) (h11 : s.gpr .x11 = q)
    (h12 : s.gpr .x12 = BitVec.ofNat 64 n) (hr : ∀ j < n, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨q, n⟩ ⟨S, oRsa⟩) :
    WP isa Impl.RsaPkcs1Sig.AArch64.copyLoop s fun t => Keep [.x15, .x11, .x14, .x12] s t ∧
      Frame [⟨S, oRsa⟩] s.mem t.mem ∧ Rep t.mem S (updL V o (Spec.Rsa.bytesAt s.mem q n)) := by
  have c6 : oRsa = 8192 := rfl
  refine WP.mono (copy_ok hn (by omega) h14 h11 h12 hr (fun i hi => by rw [off_add]; exact L.st (by omega))
    (fun j hj i hi h => hd _ (Offset.contains_base q (d := j) (n := 1) (k := n) (by omega) (by omega))
      (by rw [h, off_add]; exact Offset.contains_base S (by omega) (by omega))))
    fun t ⟨k, hm⟩ => ⟨k, ?_, ?_⟩
  · rw [hm]
    exact writeBytes_frame _ _ _ (Offset.contains_base S (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega) (by omega))
  · rw [hm]; exact R.writeBytes (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega)

/-- `copyLoop` within our working space, from `scratch + a` to `scratch + b`. -/
theorem copyWithin_ok {s : State} {F S : Addr} (L : Lay s F S) {V : Nat → Byte} (R : Rep s.mem S V)
    {a b n : Nat} (hn : 0 < n) (ha : a + n ≤ oRsa) (hb : b + n ≤ oRsa) (hab : a + n ≤ b ∨ b + n ≤ a)
    (h14 : s.gpr .x14 = off S b) (h11 : s.gpr .x11 = off S a) (h12 : s.gpr .x12 = BitVec.ofNat 64 n) :
    WP isa Impl.RsaPkcs1Sig.AArch64.copyLoop s fun t => Keep [.x15, .x11, .x14, .x12] s t ∧
      Frame [⟨S, oRsa⟩] s.mem t.mem ∧ Rep t.mem S (updL V b ((List.range n).map fun i => V (a + i))) := by
  have c6 : oRsa = 8192 := rfl
  refine WP.mono (copy_ok hn (by omega) h14 h11 h12 (fun j hj => by rw [off_add]; exact L.ld (by omega))
    (fun i hi => by rw [off_add]; exact L.st (by omega))
    (fun j hj i hi h => by rw [off_add, off_add, off_inj S (by omega) (by omega)] at h; omega))
    fun t ⟨k, hm⟩ => ⟨k, ?_, ?_⟩
  · rw [hm, R.bytes (by omega)]
    exact writeBytes_frame _ _ _ (Offset.contains_base S
      (by simp only [List.length_map, List.length_range]; omega) (by omega))
  · rw [hm, R.bytes (by omega)]
    exact R.writeBytes (by simp only [List.length_map, List.length_range]; omega)

/-- `x25 := dbLen` and `x24 := DB`, from `x9 = emLen - hLen - 2` and `lo`. -/
theorem dbRegs_ok {t : State} {F S : Addr} (L : Lay t F S) {x lo : Nat} (h9 : t.gpr .x9 = BitVec.ofNat 64 x)
    (hlo : t.mem.readW (off F sLo) 64 = BitVec.ofNat 64 lo) :
    WP isa (.block dbRegs) t fun t' => Only [.x25, .x9, .x24] t t' ∧ t'.gpr .x25 = BitVec.ofNat 64 (x + 1) ∧
      t'.gpr .x24 = off S (oEm + lo) := by
  unfold dbRegs
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_ldrSp (by decide)
    (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ => ?_
  refine wp_addImm (by decide) fun u₃ o₃ e₃ => wp_add fun u₄ o₄ e₄ => wp_nil
    ⟨(o₁.trans (o₂.trans (o₃.trans o₄))).mono, ?_, ?_⟩
  · rw [o₄.get .x25, o₃.get .x25, o₂.get .x25, e₁, h9, BitVec.ofNat_add_ofNat]
  · rw [e₄, e₃, o₃.get .x9, e₂, o₂.get .x20, o₁.get .x20, L.x20, o₁.mem, o₁.sp, L.sp, hlo, off_add]

/-- `Y`'s 2048 bytes cleared. -/
theorem clearY_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) :
    WP isa clearY t fun t' => Keep [.x10, .x9, .x12] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (clr V oY 2048) := by
  unfold clearY
  refine WP.seq (WP.mono (wp_addImm (by decide) fun u₁ o₁ e₁ => wp_movz fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x10, .x9, .x12] t u ∧ u.gpr .x10 = off S oY ∧ u.gpr .x9 = 0#64 ∧
      u.gpr .x12 = BitVec.ofNat 64 256)
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x10, o₂.get .x10, e₁, L.x20],
        by rw [o₃.get .x9, e₂]; rfl, by rw [e₃]; rfl⟩) fun u ⟨O, h10, h9, h12⟩ => ?_)
  exact WP.mono (clearQ_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) (by decide) (by decide) h10 h9 h12)
    fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, r⟩

section
variable {H : Hash} (hH : HashOK H)

include hH in
/-- `mHash` (`hLen` bytes at `dig`) after the 8 zero bytes of `Y`. -/
theorem copyDigest_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {dig : Addr} (hdg : t.mem.readW (off F sDig) 64 = dig)
    (hr : ∀ j < H.D, InRegions (t.rd ++ t.wr) (dig + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨dig, H.D⟩ ⟨S, oRsa⟩) :
    WP isa (copyDigest H) t fun t' => Keep [.x11, .x14, .x12, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V (oY + 8) (Spec.Rsa.bytesAt t.mem dig H.D)) := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold copyDigest
  refine WP.seq (WP.mono (wp_ldrSp (by decide) (ld_slot L (by decide)) fun u₁ o₁ e₁ =>
    wp_addImm (by unfold oY; omega) fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = dig ∧ u.gpr .x14 = off S (oY + 8) ∧
      u.gpr .x12 = BitVec.ofNat 64 H.D)
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, L.sp, hdg],
        by rw [o₃.get .x14, e₂, o₁.get .x20, L.x20], by rw [e₃, setWidth_ofNat16 (by omega)]⟩)
    fun u ⟨O, h11, h14, h12⟩ => ?_)
  refine WP.mono (copyIn_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) hD (by unfold oY oRsa; omega) h14 h11 h12
    (by rw [O.rd, O.wr]; exact hr) hd) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, ?_⟩
  rw [O.mem] at r; exact r

include hH in
/-- The salt (`sl` bytes at `q`) after `mHash` in `Y`. -/
theorem copySaltY_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {q : Addr} {sl : Nat} (hq : t.mem.readW (off F sSalt) 64 = q)
    (hsl : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl) (hsl' : sl ≤ 1024)
    (hr : ∀ j < sl, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨q, sl⟩ ⟨S, oRsa⟩) :
    WP isa (copySaltY H) t fun t' => Keep [.x11, .x14, .x12, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V (oY + 8 + H.D) (Spec.Rsa.bytesAt t.mem q sl)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  unfold copySaltY
  refine WP.seq (WP.mono (wp_ldrSp (by decide) (ld_slot L (by decide)) fun u₁ o₁ e₁ =>
    wp_addImm (by unfold oY; omega) fun u₂ o₂ e₂ => wp_ldrSp (by decide)
      (by rw [o₂.sp, o₂.rd, o₂.wr, o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x11, .x14, .x12] t u ∧ u.gpr .x11 = q ∧ u.gpr .x14 = off S (oY + 8 + H.D) ∧
      u.gpr .x12 = BitVec.ofNat 64 sl)
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x11, o₂.get .x11, e₁, L.sp, hq],
        by rw [o₃.get .x14, e₂, o₁.get .x20, L.x20],
        by rw [e₃, o₂.mem, o₁.mem, o₂.sp, o₁.sp, L.sp, hsl]⟩)
    fun u ⟨O, h11, h14, h12⟩ => ?_)
  refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
  · rw [h12] at h
    have h0 : sl = 0 := by
      have : (BitVec.ofNat 64 sl).toNat = 0 := by rw [beq_iff_eq.mp h]; rfl
      rw [BitVec.toNat_ofNat] at this
      omega
    subst h0
    refine wp_nil ⟨O.keep.mono, O.mem ▸ Frame.refl _ _, ?_⟩
    rw [O.mem]
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, updL_nil]
    exact R
  · rw [h12] at h
    have h0 : 0 < sl := by
      rcases Nat.eq_zero_or_pos sl with e | e
      · subst e; simp at h
      · exact e
    refine WP.mono (copyIn_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) h0 (by unfold oY oRsa; omega) h14 h11
      h12 (by rw [O.rd, O.wr]; exact hr) hd) fun v ⟨k, f, r⟩ => ⟨(O.keep.trans k).mono, O.mem ▸ f, ?_⟩
    rw [O.mem] at r; exact r

include hH in
/-- `ℓ = 8 + hLen + sLen` into `x22`, and `nbm` into its slot. -/
theorem signLen_ok {t : State} {F S : Addr} (L : Lay t F S) {sl : Nat}
    (hsl : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl) (hsl' : sl ≤ 1024) :
    WP isa (.block (signLen H)) t fun t' => Keep [.x9, .x22, .x16] t t' ∧
      t'.gpr .x22 = BitVec.ofNat 64 (8 + H.D + sl) ∧
      t'.mem = t.mem.writeW (off F sNb) (BitVec.ofNat 64 ((8 + H.D + sl + H.P.L) / H.P.B + 1)) := by
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have hL := hH.L
  have hlg : 2 ^ lgB H = H.P.B ∧ lgB H < 64 := by
    unfold lgB
    rcases hH.sizes.B with h | h <;> rw [h]
    · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
    · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide
  unfold signLen Impl.RsaPss.AArch64.lastBlk st
  simp only [List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) (ld_slot L (by decide)) fun u₁ o₁ e₁ => wp_addImm (by omega) fun u₂ o₂ e₂ => ?_
  refine wp_addImm (by omega) fun u₃ o₃ e₃ => wp_lsr hlg.2 fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ => ?_
  refine wp_addSp (by decide) fun u₆ o₆ e₆ => ?_
  have hsp : u₅.sp = F := by rw [o₅.sp, o₄.sp, o₃.sp, o₂.sp, o₁.sp, L.sp]
  refine wp_strx (by decide) (by rw [e₆, hsp, BitVec.add_zero])
    (by rw [o₆.wr, o₅.wr, o₄.wr, o₃.wr, o₂.wr, o₁.wr]; exact L.fst (by decide)) fun u₇ m₇ => wp_nil ?_
  have x22 : u₂.gpr .x22 = BitVec.ofNat 64 (8 + H.D + sl) := by
    rw [e₂, e₁, L.sp, hsl, BitVec.ofNat_add_ofNat, Nat.add_comm sl]
  refine ⟨(o₁.keep.trans (o₂.keep.trans (o₃.keep.trans (o₄.keep.trans (o₅.keep.trans (o₆.keep.trans
    m₇.keep)))))).mono, by rw [m₇.gpr, o₆.get .x22, o₅.get .x22, o₄.get .x22, o₃.get .x22, x22], ?_⟩
  rw [m₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem, o₆.get .x9, e₅, e₄, e₃, x22,
    BitVec.ofNat_add_ofNat, lsr_val (by omega), hlg.1, BitVec.ofNat_add_ofNat]

/-- `EM`'s `k` bytes cleared. -/
theorem clearEm_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V) {k : Nat}
    (h23 : t.gpr .x23 = BitVec.ofNat 64 k) (hk : 0 < k) (hk' : k ≤ 1024) :
    WP isa clearEm t fun t' => Keep [.x14, .x13, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL V oEm (List.replicate k 0)) := by
  have c1 : oEm = 2560 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold clearEm
  refine WP.seq (WP.mono (wp_addImm (by decide) fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
    wp_nil (Q := fun u => Only [.x14, .x13, .x15] t u ∧ u.gpr .x14 = off S oEm ∧ u.gpr .x13 = BitVec.ofNat 64 k ∧
      (u.gpr .x15).setWidth 8 = 0)
      ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x14, o₂.get .x14, e₁, L.x20],
        by rw [o₃.get .x13, e₂, o₁.get .x23, h23], by rw [e₃]; rfl⟩) fun u ⟨O, h14, h13, h15⟩ => ?_)
  have Lu := L.congr O.sp O.wr (O.get .x20)
  refine WP.mono (fill_ok hk (by omega) h14 h13 h15 fun i hi => by rw [off_add]; exact Lu.st (by omega))
    fun v ⟨k', hm⟩ => ⟨(O.keep.trans k').mono, ?_, ?_⟩
  · rw [hm, O.mem]
    exact writeBytes_frame _ _ _ (Offset.contains_base S (by rw [List.length_replicate]; omega) (by omega))
  · rw [hm, O.mem]; exact R.writeBytes (by rw [List.length_replicate]; omega)

theorem Lay.slotSd {t : State} {F S : Addr} (L : Lay t F S) {d : Nat} (hd : d + 8 ≤ frameBytes) :
    ∀ r ∈ [(⟨S, oRsa⟩ : Region)], Region.Disjoint (slotR F d) r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact L.dFS.sub_left (Offset.sub_base F hd)

theorem wS_frame (m : Mem) (S : Addr) {x : Nat} (hx : x + 1 ≤ oRsa) (b : Byte) :
    Frame [⟨S, oRsa⟩] m (m.writeW (off S x) b) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base S hx (by unfold oRsa at hx; omega))

theorem off_sub (p : Addr) {a b : Nat} (h : b ≤ a) : off p a - BitVec.ofNat 64 b = off p (a - b) := by
  rw [BitVec.sub_eq_iff_eq_add, off_add, Nat.sub_add_cancel h]

/-- `0x01` at `DB + dbLen - sLen - 1`, and the salt after it. -/
theorem putSalt_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {e db : Nat} (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    {q : Addr} {sl : Nat} (hq : t.mem.readW (off F sSalt) 64 = q)
    (hsl : t.mem.readW (off F sSaltLen) 64 = BitVec.ofNat 64 sl) (hfit : sl + 1 ≤ db) (he : e + db ≤ oY)
    (hr : ∀ j < sl, InRegions (t.rd ++ t.wr) (q + BitVec.ofNat 64 j) 1)
    (hd : Region.Disjoint ⟨q, sl⟩ ⟨S, oRsa⟩) :
    WP isa putSalt t fun t' => Keep [.x14, .x12, .x9, .x11, .x15] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (updL (upd V (e + db - sl - 1) 1) (e + db - sl) (Spec.Rsa.bytesAt t.mem q sl)) := by
  have c2 : oY = 3584 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold putSalt
  refine WP.seq (WP.mono (Q := fun (u : State) => Keep [.x14, .x12, .x9, .x11] t u ∧ u.gpr .x14 = off S (e + db - sl) ∧
      u.gpr .x12 = BitVec.ofNat 64 sl ∧ u.gpr .x11 = q ∧ u.mem = t.mem.writeW (off S (e + db - sl - 1)) (1 : Byte))
    ?_ fun u ⟨K, h14, h12, h11, hm⟩ => ?_)
  · refine wp_add fun u₁ o₁ e₁ => wp_ldrSp (by decide)
      (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ =>
      wp_sub fun u₃ o₃ e₃ => wp_subImm (by decide) fun u₄ o₄ e₄ => wp_movz fun u₅ o₅ e₅ => ?_
    have h12 : u₂.gpr .x12 = BitVec.ofNat 64 sl := by rw [e₂, o₁.mem, o₁.sp, L.sp, hsl]
    have h14 : u₅.gpr .x14 = off S (e + db - sl - 1) := by
      rw [o₅.get .x14, e₄, e₃, o₂.get .x14, e₁, h24, h25, off_add, h12, off_sub _ (by omega),
        off_sub _ (by omega)]
    have O₅ : Only [.x14, .x12, .x9] t u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
    refine wp_strb (by decide) (by rw [h14, BitVec.add_zero]) (by rw [O₅.wr]; exact L.st (by omega))
      fun u₆ m₆ => wp_addImm (by decide) fun u₇ o₇ e₇ => wp_ldrSp (by decide)
        (by rw [o₇.sp, o₇.rd, o₇.wr, m₆.sp, m₆.rd, m₆.wr, O₅.sp, O₅.rd, O₅.wr]; exact ld_slot L (by decide))
        fun u₈ o₈ e₈ => wp_nil ⟨(O₅.keep.trans (m₆.keep.trans (o₇.keep.trans o₈.keep))).mono, ?_, ?_, ?_, ?_⟩
    · rw [o₈.get .x14, e₇, m₆.gpr, h14, off_add, show e + db - sl - 1 + 1 = e + db - sl by omega]
    · rw [o₈.get .x12, o₇.get .x12, m₆.gpr, o₅.get .x12, o₄.get .x12, o₃.get .x12, h12]
    · rw [e₈, o₇.mem, m₆.mem, O₅.mem, o₇.sp, m₆.sp, O₅.sp, L.sp,
        slot_keep (wS_frame _ S (by omega) _) (L.slotSd (by decide)), hq]
    · rw [o₈.mem, o₇.mem, m₆.mem, O₅.mem, e₅]; rfl
  have Lu : Lay u F S := L.congr K.sp K.wr (K.get .x20)
  have Ru : Rep u.mem S (upd V (e + db - sl - 1) 1) := by rw [hm]; exact R.wb (by omega) _
  have Fu : Frame [⟨S, oRsa⟩] t.mem u.mem := by rw [hm]; exact wS_frame _ S (by omega) _
  refine WP.ite _ (eval_zero _ _) (fun h => ?_) (fun h => ?_)
  · rw [h12] at h
    have h0 : sl = 0 := by
      have : (BitVec.ofNat 64 sl).toNat = 0 := by rw [beq_iff_eq.mp h]; rfl
      rw [BitVec.toNat_ofNat] at this
      omega
    subst h0
    refine wp_nil ⟨K.mono, Fu, ?_⟩
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, updL_nil]
    exact Ru
  · rw [h12] at h
    have h0 : 0 < sl := by
      rcases Nat.eq_zero_or_pos sl with e' | e'
      · subst e'; simp at h
      · exact e'
    have hb : Spec.Rsa.bytesAt u.mem q sl = Spec.Rsa.bytesAt t.mem q sl :=
      VG.Proof.RsaPkcs1Sig.bytes_apart (R := ⟨q, sl⟩) Fu hd (by show sl ≤ 2 ^ 64; omega)
    refine WP.mono (copyIn_ok Lu Ru h0 (by omega) h14 h11 h12 (by rw [K.rd, K.wr]; exact hr) hd)
      fun v ⟨k, f, r⟩ => ⟨(K.trans k).mono, Fu.trans f, ?_⟩
    rw [hb] at r; exact r

include hH in
/-- `H` (the digest at `oDig`) after `DB`, and `0xbc` at `EM`'s last byte. -/
theorem putH_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {e db k : Nat} (h24 : t.gpr .x24 = off S e) (h25 : t.gpr .x25 = BitVec.ofNat 64 db)
    (h21 : t.gpr .x21 = off S oDig) (h23 : t.gpr .x23 = BitVec.ofNat 64 k) (he : oEm ≤ e)
    (hk : e + db + H.D + 1 = oEm + k) (hk' : k ≤ 1024) :
    WP isa (putH H) t fun t' => Keep [.x14, .x11, .x12, .x15, .x9, .x10] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (upd (updL V (e + db) ((List.range H.D).map fun i => V (oDig + i))) (oEm + k - 1) 0xbc) := by
  have hD := hH.sizes.D0
  have hDN := hH.sizes.DN
  have hN := hH.N_le
  have c1 : oEm = 2560 := rfl
  have c3 : oDig = 2304 := rfl
  have c6 : oRsa = 8192 := rfl
  unfold putH
  refine WP.seq (WP.mono (Q := fun (v : State) => Keep [.x14, .x11, .x12, .x15] t v ∧
      Frame [⟨S, oRsa⟩] t.mem v.mem ∧ Rep v.mem S (updL V (e + db) ((List.range H.D).map fun i => V (oDig + i))))
    ?_ fun v ⟨K, Fv, Rv⟩ => ?_)
  · refine WP.seq (WP.mono (wp_add fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_movz fun u₃ o₃ e₃ =>
      wp_nil (Q := fun (u : State) => Only [.x14, .x11, .x12] t u ∧ u.gpr .x14 = off S (e + db) ∧
        u.gpr .x11 = off S oDig ∧ u.gpr .x12 = BitVec.ofNat 64 H.D)
        ⟨(o₁.trans (o₂.trans o₃)).mono, by rw [o₃.get .x14, o₂.get .x14, e₁, h24, h25, off_add],
          by rw [o₃.get .x11, e₂, o₁.get .x21, h21], by rw [e₃, setWidth_ofNat16 (by omega)]⟩)
      fun u ⟨O, h14, h11, h12⟩ => ?_)
    exact WP.mono (copyWithin_ok (L.congr O.sp O.wr (O.get .x20)) (O.mem ▸ R) hD (by omega) (by omega)
      (by omega) h14 h11 h12) fun v ⟨k', f, r⟩ => ⟨(O.keep.trans k').mono, O.mem ▸ f, r⟩
  refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_add fun u₂ o₂ e₂ => wp_subImm (by decide) fun u₃ o₃ e₃ =>
    wp_movz fun u₄ o₄ e₄ => ?_
  have h9 : u₄.gpr .x9 = off S (oEm + k - 1) := by
    rw [o₄.get .x9, e₃, e₂, o₁.get .x23, K.get .x23, h23, e₁, K.get .x20, L.x20, off_add, off_sub _ (by omega)]
  have O₄ : Only [.x9, .x10] v u₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  refine wp_strb (by decide) (by rw [h9, BitVec.add_zero]) (by rw [O₄.wr, K.wr]; exact L.st (by omega))
    fun u₅ m₅ => wp_nil ⟨(K.trans (O₄.keep.trans m₅.keep)).mono, ?_, ?_⟩
  · rw [m₅.mem, O₄.mem]; exact Fv.trans (wS_frame _ S (by omega) _)
  · rw [m₅.mem, O₄.mem, e₄]; exact Rv.wb (by omega) _

theorem trunc_and (x y : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x &&& BitVec.setWidth 64 y) = x &&& y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := y.toNat) (by omega),
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega))]

/-- `DB`'s first byte ANDed with the mask `c` (`sC`). -/
theorem clearTop_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} (R : Rep t.mem S V)
    {e : Nat} {c : Byte} (h24 : t.gpr .x24 = off S e) (he : e < oRsa)
    (hc : t.mem.readW (off F sC) 64 = BitVec.setWidth 64 c) :
    WP isa (.block clearTop) t fun t' => Keep [.x9, .x10] t t' ∧ Frame [⟨S, oRsa⟩] t.mem t'.mem ∧
      Rep t'.mem S (upd V e (V e &&& c)) := by
  unfold clearTop
  refine wp_ldrb (by decide) (by rw [h24, BitVec.add_zero]) (L.ld (by omega)) fun u₁ o₁ e₁ => ?_
  refine wp_ldrSp (by decide) (by rw [o₁.sp, o₁.rd, o₁.wr]; exact ld_slot L (by decide)) fun u₂ o₂ e₂ =>
    wp_and fun u₃ o₃ e₃ => ?_
  have O₃ : Only [.x9, .x10] t u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine wp_strb (by decide) (by rw [O₃.get .x24, h24, BitVec.add_zero]) (by rw [O₃.wr]; exact L.st (by omega))
    fun u₄ m₄ => wp_nil ⟨(O₃.keep.trans m₄.keep).mono, ?_, ?_⟩
  · rw [m₄.mem, O₃.mem]; exact wS_frame _ S (by omega) _
  · have hv : (u₃.gpr .x9).setWidth 8 = V e &&& c := by
      rw [e₃, o₂.get .x9, e₁, e₂, o₁.mem, o₁.sp, L.sp, hc, R e he, trunc_and]
    rw [m₄.mem, O₃.mem, hv]; exact R.wb he _

end

end VG.Proof.RsaPss.AArch64