import VerifiedGarbage.Proof.RsaPss.X86_64.Basic
import VerifiedGarbage.Proof.RsaPss.CtPad
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core

/-!
# RSASSA-PSS on x86-64: hashing a message of secret length

`ctHash` (`Impl/RsaPss/X86_64.lean`) leaves the digest of the first `ℓ`
bytes of `Y` at `scratch + oDig`, for a hash function whose code the proofs
know (`HashOK`), from a state where those bytes are followed by zeros up to
`nbm` blocks (`ctHash_ok`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn load64_eq store64_eq)
open VG.Proof.Bignum.X86_64 (off word Scr off_off ofNat_add_one ofNat_sub_beq wp_upto)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable {H : Hash} (hH : HashOK H) (K : Callees H)

theorem slot_eq (d : Nat) (k : Nat) (h : d = 8 * k) (m : Mem) (F : Addr) : word m F d = word m F (8 * k) := by
  rw [h]

/-- `scratch + o` into `d`. -/
theorem scr_ok {t : State} {F S : Addr} (L : Lay t F S) {d : Reg} (hd : d ≠ .rsp) {o : Nat} (ho : o < 2 ^ 31) :
    WP isa (.block (scr d o)) t fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem ∧ Keep [d] t t' := by
  refine WP.mono (WP.keep [d] (Q := fun t' => t'.gpr d = off S o ∧ t'.mem = t.mem) ?_ ?_) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  · have hl := L.ld (d := sScr) (by decide)
    have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    xrun [scr, ea_sp, L.rsp, hl, hs, VG.Proof.MlKem.X86_64.sx_ofNat ho]
  · cases d <;> first | exact absurd rfl hd | rfl

/-- What a call leaves of the frame: `Lay`, and the view of memory with the
ranges `rgs` it may write read again. -/
theorem Lay.after_call {t t' : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hF : Frame (regs S rgs ++ [retR F]) t.mem t'.mem) (hsp : t'.gpr .rsp = t.gpr .rsp) (hwr : t'.wr = t.wr) :
    Lay t' F S ∧ Rep t'.mem F S (fun o => if inR rgs o then t'.mem (off S o) else V o) W := by
  have R' := R.frame L.geo hrg hF
  refine ⟨L.congr hsp hwr ?_, R'⟩
  rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R'.fr 21 (by decide), R.fr 21 (by decide)]

/-- A callee-saved register is not `rdi`. -/
theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) : r ∉ [Reg.rdi] := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

include K in
/-- The streaming `init` on `scratch + oSt`: its hash value is the initial one. -/
theorem ctInit_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) :
    WP isa (ctInit H) t fun t' => Lay t' F S ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) ∧
      Rep t'.mem F S (fun o => if inR [(oSt, H.P.N + H.P.B)] o then t'.mem (off S o) else V o) W ∧
      hH.md.stateAt t'.mem (off S oSt) = hH.iv := by
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega
  refine WP.seq (WP.mono (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u ⟨hdi, hm, hk⟩ => ?_)
  have Lu : Lay u F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have Ru : Rep u.mem F S V W := hm ▸ R
  refine WP.call (k := initK (H.P.N + H.P.B) hH.SH.Repr) hH.init.1 hH.initSp (by rw [K.iD]; decide)
    (rd := []) (wr := [⟨off S oSt, H.P.N + H.P.B⟩]) ?_ ?_ (Lu.cov (by unfold oSt oRsa; omega)) ?_
  · simp only [initK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hdi, Lu.rsp, true_and]
    exact Region.Disjoint.sub_right L.dRS (Offset.sub_base S (by unfold oSt oRsa; omega))
  · exact Covers.right (Lu.cov (by unfold oSt oRsa; omega))
  · intro t' hrd hwr hcs hF _ ⟨s₂, hm₂, _, hpost⟩
    simp only [initK, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), hdi, hm₂]
      at hpost
    rw [K.iD, Lu.rsp] at hF
    obtain ⟨L', R'⟩ := Lu.after_call Ru (rgs := [(oSt, H.P.N + H.P.B)])
      (by simp only [List.mem_singleton]; rintro p rfl; unfold oSt oRsa; omega) hF
      (hcs .rsp (by decide)) hwr
    refine ⟨L', hrd.trans hk.2.1, hwr.trans hk.2.2, fun r hr => (hcs r hr).trans ?_, R', ?_⟩
    · exact hk.gpr (cs_ne hr)
    · obtain ⟨h1, -⟩ := (hH.repr _ _ _).1 hpost
      rw [h1, List.length_nil, Nat.zero_div, MdStream.Md.compressList_zero]

/-! ## Facts about the sizes -/

theorem ror_mul {x k B : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 63) (hB : 2 ^ k = B) (hx : x * B < 2 ^ 64) :
    (BitVec.ofNat 64 x).rotateRight (64 - k) = BitVec.ofNat 64 (x * B) := by
  subst hB
  apply BitVec.eq_of_toNat_eq
  have hx' : x < 2 ^ (64 - k) := by
    have : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
    rw [this] at hx
    exact Nat.lt_of_mul_lt_mul_right hx
  have hx64 : x < 2 ^ 64 := Nat.lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by decide) (by omega))
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hx]
  rw [Nat.mod_eq_of_lt (show 64 - k < 64 by omega), Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx',
    Nat.zero_or, Nat.shiftLeft_eq, show 64 - (64 - k) = k by omega, Nat.mod_eq_of_lt hx]

include hH in
theorem lgB_spec : 2 ^ lgB H = H.P.B ∧ 6 ≤ lgB H ∧ lgB H ≤ 7 := by
  unfold lgB
  rcases hH.dims.B with h | h <;> rw [h] <;> decide

theorem mask80 : ∀ (b : Byte) (c : Bool), (BitVec.setWidth 64 b ||| (0#64 - BitVec.setWidth 64 (BitVec.ofBool c) &&&
    BitVec.signExtend 64 (128 : BitVec 32))).setWidth 8 = b ||| (if c then 0x80 else 0) := by
  decide

/-- `Lay` after a block that changed memory only as `Rep` says, keeping `W`. -/
theorem Lay.of_rep {u u' : State} {F S : Addr} (L : Lay u F S) {V V' : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) (R' : Rep u'.mem F S V' W) (hsp : u'.gpr .rsp = u.gpr .rsp) (hwr : u'.wr = u.wr) :
    Lay u' F S :=
  L.congr hsp hwr (by rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, R'.fr 21 (by decide), R.fr 21 (by decide)])

/-! ## `0x80` -/

/-- `Y` with `0x80` ORed into byte `ℓ`, over its first `j` bytes. -/
def v80 (V : Nat → Byte) (ℓ j : Nat) (o : Nat) : Byte :=
  if oY ≤ o ∧ o < oY + j then V o ||| (if o - oY = ℓ then 0x80 else 0) else V o

structure P80 (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (ℓ N j : Nat) (u : State) : Prop where
  L : Lay u F S
  keep : Keep [.rcx, .rdx, .r10, .r8, .rax, .r9] t u
  rcx : u.gpr .rcx = off S oY
  rdx : u.gpr .rdx = BitVec.ofNat 64 ℓ
  r10 : u.gpr .r10 = BitVec.ofNat 64 N
  r8 : u.gpr .r8 = BitVec.ofNat 64 j
  R : Rep u.mem F S (v80 V ℓ j) W

include hH in
theorem pad80_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ nbm : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ) (hn : W 28 = BitVec.ofNat 64 nbm)
    (h1 : 1 ≤ nbm) (hnb : nbm * H.P.B ≤ 2048) (hℓ : ℓ < 2 ^ 63) :
    WP isa (pad80 H) t fun t' => P80 t F S V W ℓ (nbm * H.P.B) (nbm * H.P.B) t' := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hB := hH.B_pos
  have hN : nbm * H.P.B < 2 ^ 63 := by omega
  refine WP.seq (WP.mono (WP.keep [.rcx, .rdx, .r10, .r8, .rax, .r9] (Q := fun u => u.gpr .rcx = off S oY ∧
      u.gpr .rdx = BitVec.ofNat 64 ℓ ∧ u.gpr .r10 = BitVec.ofNat 64 (nbm * H.P.B) ∧
      u.gpr .r8 = BitVec.ofNat 64 0 ∧ u.mem = t.mem) ?_ rfl) fun u ⟨⟨h₁, h₂, h₃, h₄, hm⟩, hk⟩ => ?_)
  · have hs := L.slot
    simp only [Bignum.X86_64.word] at hs
    have e27 : t.mem.readW (off F sL) 64 = BitVec.ofNat 64 ℓ := by
      rw [← hl, ← R.fr 27 (by decide)]; rfl
    have e28 : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by
      rw [← hn, ← R.fr 28 (by decide)]; rfl
    xrun [pad80, scr, ea_sp, L.rsp, L.ld (d := sScr) (by decide), L.ld (d := sL) (by decide),
      L.ld (d := sNb) (by decide), hs, e27, e28, VG.Proof.MlKem.X86_64.sx_ofNat (show oY < 2 ^ 31 by decide),
      ror_mul (x := nbm) (k := lgB H) (B := H.P.B) (by omega) (by omega) hpow (show nbm * H.P.B < 2 ^ 64 by omega), List.cons_append,
      List.nil_append, show 1 ≤ 64 - lgB H ∧ 64 - lgB H ≤ 63 from ⟨by omega, by omega⟩,
      show ¬ 64 - lgB H = 1 by omega]
  · refine wp_upto (a := 0) (N := nbm * H.P.B) (Nat.mul_pos (by omega) hB) (P80 t F S V W ℓ (nbm * H.P.B)) ?_ (fun _ h => h)
      ⟨L.of_rep R (hm ▸ R) (hk.gpr (by decide)) hk.2.2 |> fun L' => L', hk, h₁, h₂, h₃, h₄, ?_⟩
    · intro j _ hj u I
      have hld := I.L.sld8 (d := oY + j) (by unfold oY oRsa; omega)
      have hst := I.L.sst8 (d := oY + j) (by unfold oY oRsa; omega)
      have hea : off S oY + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (oY + j) := by
        rw [off_ix, off_off, Nat.add_zero]
      refine WP.mono (WP.keep [.rax, .r9, .r8] (Q := fun u' => u'.zf = some (decide (j + 1 = nbm * H.P.B)) ∧
          u'.gpr .r8 = BitVec.ofNat 64 (j + 1) ∧
          u'.mem = u.mem.writeW (off S (oY + j)) (u.mem (off S (oY + j)) ||| if j = ℓ then 0x80 else 0)) ?_ rfl)
        fun u' ⟨⟨hz, h8', hm'⟩, hk'⟩ => ⟨hz, ?_⟩
      · xrun [step, List.cons_append, List.nil_append, ea_ix, I.rcx, hea, hld, hst, I.r8, I.rdx, I.r10,
          xor_lt_one (show j < 2 ^ 64 by omega) (show ℓ < 2 ^ 64 by omega), mask80, decide_eq_true_eq, ofNat_add_lit,
          ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show nbm * H.P.B < 2 ^ 64 by omega)]
      · have R' : Rep u'.mem F S (v80 V ℓ (j + 1)) W := by
          rw [hm']
          have := I.R.wb I.L.geo (o := oY + j) (by unfold oY oRsa; omega)
            (u.mem (off S (oY + j)) ||| if j = ℓ then 0x80 else 0)
          refine (congrArg (fun V' => Rep _ F S V' W) (funext fun o => ?_)).mpr this
          simp only [v80, upd, I.R.scr (oY + j) (by unfold oY oRsa; omega)]
          by_cases h : o = oY + j
          · subst h; simp
          · by_cases h' : oY ≤ o ∧ o < oY + j <;> simp [h, h'] <;> omega
        exact ⟨I.L.of_rep I.R R' (hk'.gpr (by decide)) hk'.2.2, (I.keep.trans hk').mono (by decide),
          (hk'.gpr (by decide)).trans I.rcx, (hk'.gpr (by decide)).trans I.rdx, (hk'.gpr (by decide)).trans I.r10,
          h8', R'⟩
    · rw [hm]
      refine (congrArg (fun V' => Rep _ F S V' W) (funext fun o => ?_)).mpr R
      simp only [v80, Nat.add_zero]
      split
      · omega
      · rfl

/-! ## The length field -/

/-- The working space with the length field of `ℓ` at `oLen`. -/
def lenV (V : Nat → Byte) (len : List Byte) (o : Nat) : Byte :=
  if oLen ≤ o ∧ o < oLen + len.length then len.getD (o - oLen) 0 else V o

include hH in
theorem lenField_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {ℓ : Nat} (hl : W 27 = BitVec.ofNat 64 ℓ) (hℓ : ℓ < 2 ^ 62) :
    WP isa (.block (lenField H)) t fun t' => Lay t' F S ∧ Keep [.rbx, .r12, .rax] t t' ∧
      Rep t'.mem F S (lenV V (hH.md.lenBytes ℓ)) (upd W 30 (BitVec.ofNat 64 (RsaPss.lastBlk H.P.B H.P.L ℓ))) := by
  obtain ⟨hpow, hlg1, hlg2⟩ := lgB_spec hH
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega
  have hL := hH.dims.L
  have e27 : t.mem.readW (off F sL) 64 = BitVec.ofNat 64 ℓ := by rw [← hl, ← R.fr 27 (by decide)]; rfl
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  rw [lenField, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rbx, .r12] (Q := fun u => u.gpr .rbx = off S (oLen - (H.P.N + H.P.B - H.P.L)) ∧
      u.gpr .r12 = BitVec.ofNat 64 ℓ ∧ u.mem = t.mem) ?_ rfl) fun u ⟨⟨h₁, h₂, hm⟩, hk⟩ => ?_
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sL) (by decide), hs, e27,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLen - (H.P.N + H.P.B - H.P.L) < 2 ^ 31 by unfold oLen; omega)]
  have Lu : Lay u F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  have ea : u.gpr .rbx + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L) = off S oLen := by
    rw [h₁]; show off (off S _) _ = _; rw [off_off]; congr 1; unfold oLen; omega
  have hin : InRegions u.wr (u.gpr .rbx + BitVec.ofNat 64 (H.P.N + H.P.B - H.P.L)) H.P.L := by
    rw [ea]; exact Lu.cov (o := oLen) (n := H.P.L) (by unfold oLen oRsa; omega) _ _
      ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (hH.shape.len u hin) fun v ⟨hg, hrd, hwr, hmv⟩ => ?_
  have hlen : hH.md.lenOf (BitVec.ofNat 64 ℓ) = hH.md.lenBytes ℓ :=
    hH.md.lenOf_eq ℓ (hH.lenOk ℓ (by omega))
  have Rv : Rep v.mem F S (lenV V (hH.md.lenBytes ℓ)) W := by
    rw [hmv, ea, h₂, hlen, hm]
    exact R.wbs L.geo (by rw [hH.md.lenBytes_length]; unfold oLen oRsa; omega)
  have Lv : Lay v F S := Lu.of_rep (hm ▸ R) Rv (hg .rsp (by decide)) hwr
  have e27' : v.mem.readW (off F sL) 64 = BitVec.ofNat 64 ℓ := by rw [← hl, ← Rv.fr 27 (by decide)]; rfl
  refine WP.mono (WP.keep [.rax] (Q := fun v' => v'.mem = v.mem.writeW (off F sFb)
      (BitVec.ofNat 64 (RsaPss.lastBlk H.P.B H.P.L ℓ))) ?_ rfl) fun v' ⟨hm', hk'⟩ => ?_
  · have hsh : (BitVec.ofNat 64 ℓ + BitVec.ofNat 64 H.P.L) >>> lgB H =
        BitVec.ofNat 64 (RsaPss.lastBlk H.P.B H.P.L ℓ) := by
      rw [← BitVec.ofNat_add, shr_ofNat (lgB H) (show ℓ + H.P.L < 2 ^ 64 by omega), hpow]; rfl
    xrun [ea_sp, Lv.rsp, Lv.ld (d := sL) (by decide), Lv.st (d := sFb) (by decide), e27',
      VG.Proof.MlKem.X86_64.sx_ofNat (show H.P.L < 2 ^ 31 by omega), hsh,
      show 1 ≤ lgB H ∧ lgB H ≤ 63 from ⟨by omega, by omega⟩]
  have Rv' := Rv.wf Lv.geo (k := 30) (by decide) (BitVec.ofNat 64 (RsaPss.lastBlk H.P.B H.P.L ℓ))
  rw [show off F (8 * 30) = off F sFb from rfl, ← hm'] at Rv'
  refine ⟨Lv.congr (hk'.gpr (by decide)) hk'.2.2 ?_, ?_, Rv'⟩
  · rw [slot_eq sScr 21 rfl, slot_eq sScr 21 rfl, Rv'.fr 21 (by decide), Rv.fr 21 (by decide)]; rfl
  · refine ⟨fun r hr => ?_, hk'.2.1.trans (hrd.trans hk.2.1), hk'.2.2.trans (hwr.trans hk.2.2)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [hk'.gpr (by simp [hr.2.2]), hg r hr.2.2, hk.gpr (by simp [hr.1, hr.2.1])]

/-! ## The length field in the last block -/

/-- The working space with the first `cnt` bytes of the length field `len`
ORed into the last `L` bytes of block `fb` of `Y`. -/
def lenAt (V : Nat → Byte) (len : List Byte) (B Lf fb cnt : Nat) (o : Nat) : Byte :=
  if oY + B * fb + (B - Lf) ≤ o ∧ o < oY + B * fb + (B - Lf) + cnt then
    V o ||| len.getD (o - (oY + B * fb + (B - Lf))) 0
  else V o

theorem lenAt_step (V : Nat → Byte) (len : List Byte) {B Lf fb b j : Nat} :
    upd (lenAt V len B Lf fb (if fb < b then Lf else if fb = b then j else 0)) (oY + B * b + (B - Lf) + j)
      (lenAt V len B Lf fb (if fb < b then Lf else if fb = b then j else 0) (oY + B * b + (B - Lf) + j) |||
        if b = fb then len.getD j 0 else 0) =
    lenAt V len B Lf fb (if fb < b then Lf else if fb = b then j + 1 else 0) := by
  by_cases hbf : b = fb
  · subst hbf
    funext x
    simp only [upd, lenAt, Nat.lt_irrefl, ite_true, ite_false]
    by_cases hx : x = oY + B * b + (B - Lf) + j
    · subst hx
      have h2 : oY + B * b + (B - Lf) ≤ oY + B * b + (B - Lf) + j ∧
          oY + B * b + (B - Lf) + j < oY + B * b + (B - Lf) + (j + 1) := by omega
      simp only [h2, ite_true, ite_false, and_false, and_self,
        show oY + B * b + (B - Lf) + j - (oY + B * b + (B - Lf)) = j by omega]
    · rw [ifn hx]
      by_cases h' : oY + B * b + (B - Lf) ≤ x ∧ x < oY + B * b + (B - Lf) + j
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · have oz : ∀ x : Byte, x ||| 0 = x := fun x => BitVec.or_zero
    simp only [hbf, ite_false, oz, upd_self]
    by_cases h1 : fb < b <;> simp only [h1, ite_true, ite_false, show ¬ fb = b from fun h => hbf h.symm]

/-- The registers of the loops over the blocks. -/
structure LRegs (t : State) (F S : Addr) (B Lf fb nbm b : Nat) (u : State) : Prop where
  L : Lay u F S
  keep : Keep [.rcx, .rsi, .rdx, .r10, .r8, .r11, .r9, .rax, .rdi] t u
  rcx : u.gpr .rcx = off S (oY + B * b + (B - Lf))
  rsi : u.gpr .rsi = off S oLen
  rdx : u.gpr .rdx = BitVec.ofNat 64 fb
  r10 : u.gpr .r10 = BitVec.ofNat 64 nbm
  r8 : u.gpr .r8 = BitVec.ofNat 64 b

/-- Before block `b`. -/
structure LO (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (len : List Byte)
    (B Lf fb nbm b : Nat) (u : State) : Prop extends LRegs t F S B Lf fb nbm b u where
  R : Rep u.mem F S (lenAt V len B Lf fb (if fb < b then Lf else 0)) W

/-- Within block `b`, after `j` bytes. -/
structure LI (t : State) (F S : Addr) (V : Nat → Byte) (W : Nat → BitVec 64) (len : List Byte)
    (B Lf fb nbm b j : Nat) (u : State) : Prop extends LRegs t F S B Lf fb nbm b u where
  r9 : u.gpr .r9 = BitVec.ofNat 64 j
  r11 : u.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (b = fb)))
  R : Rep u.mem F S (lenAt V len B Lf fb (if fb < b then Lf else if fb = b then j else 0)) W

include hH in
theorem lenLoop_ok {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) {len : List Byte}
    (hlen : ∀ i < H.P.L, V (oLen + i) = len.getD i 0) {fb nbm : Nat}
    (hf : W 30 = BitVec.ofNat 64 fb) (hn : W 28 = BitVec.ofNat 64 nbm) (hfb : fb < nbm)
    (hnb : nbm * H.P.B ≤ 2048) :
    WP isa (lenLoop H) t fun t' => LO t F S V W len H.P.B H.P.L fb nbm nbm t' := by
  have hB := hH.B_le
  have hB0 := hH.B_pos
  have hL := hH.dims.L
  have hLB := hH.hNL
  have hN0 := hH.dims.N
  have hnbm : nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right nbm hB0) hnb
  have hs := L.slot
  simp only [Bignum.X86_64.word] at hs
  have e30 : t.mem.readW (off F sFb) 64 = BitVec.ofNat 64 fb := by rw [← hf, ← R.fr 30 (by decide)]; rfl
  have e28 : t.mem.readW (off F sNb) 64 = BitVec.ofNat 64 nbm := by rw [← hn, ← R.fr 28 (by decide)]; rfl
  refine WP.seq (WP.mono (WP.keep [.rcx, .rsi, .rdx, .r10, .r8, .r11, .r9, .rax, .rdi] (Q := fun u =>
      u.gpr .rcx = off S (oY + H.P.B * 0 + (H.P.B - H.P.L)) ∧ u.gpr .rsi = off S oLen ∧
      u.gpr .rdx = BitVec.ofNat 64 fb ∧ u.gpr .r10 = BitVec.ofNat 64 nbm ∧ u.gpr .r8 = BitVec.ofNat 64 0 ∧
      u.mem = t.mem) ?_ rfl) fun u ⟨⟨h₁, h₂, h₃, h₄, h₅, hm⟩, hk⟩ => ?_)
  · xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide),
      L.ld (d := sFb) (by decide), L.ld (d := sNb) (by decide), hs, e30, e28,
      VG.Proof.MlKem.X86_64.sx_ofNat (show oY + H.P.B - H.P.L < 2 ^ 31 by unfold oY; omega),
      VG.Proof.MlKem.X86_64.sx_ofNat (show oLen < 2 ^ 31 by decide)]
    rw [Nat.mul_zero, Nat.add_zero, show oY + H.P.B - H.P.L = oY + (H.P.B - H.P.L) by omega]
  have Lu : Lay u F S := L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm])
  refine wp_upto (a := 0) (N := nbm) (by omega) (LO t F S V W len H.P.B H.P.L fb nbm) ?_ (fun _ h => h)
    ⟨⟨Lu, hk, h₁, h₂, h₃, h₄, h₅⟩, hm ▸ (congrArg (fun V' => Rep t.mem F S V' W)
      (funext fun o => by
        simp only [lenAt, Nat.not_lt_zero, ite_false, Nat.add_zero]; split <;> first | omega | rfl)).mpr R⟩
  intro b _ hb u I
  -- The mask and the inner counter.
  refine WP.seq (WP.mono (WP.keep [.r11, .r9] (Q := fun v =>
      v.gpr .r11 = 0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (b = fb))) ∧ v.gpr .r9 = BitVec.ofNat 64 0 ∧
      v.mem = u.mem) ?_ rfl) fun v ⟨⟨g₁, g₂, gm⟩, gk⟩ => ?_)
  · xrun [eqMask, List.cons_append, List.nil_append, I.r8, I.rdx,
      xor_lt_one (show b < 2 ^ 64 by omega) (show fb < 2 ^ 64 by omega)]
  have Lv : Lay v F S := I.L.congr (gk.gpr (by decide)) gk.2.2 (by rw [gm])
  have rg : LRegs t F S H.P.B H.P.L fb nbm b v :=
    ⟨Lv, (I.keep.trans gk).mono (by decide), (gk.gpr (by decide)).trans I.rcx, (gk.gpr (by decide)).trans I.rsi,
      (gk.gpr (by decide)).trans I.rdx, (gk.gpr (by decide)).trans I.r10, (gk.gpr (by decide)).trans I.r8⟩
  have I0 : LI t F S V W len H.P.B H.P.L fb nbm b 0 v := { rg with
    r9 := g₂, r11 := g₁,
    R := gm ▸ (congrArg (fun V' => Rep u.mem F S V' W) (funext fun o => by
      simp only [lenAt]; by_cases h1 : fb < b <;> by_cases h2 : fb = b <;>
        simp only [h1, h2, ite_true, ite_false])).mpr I.R }
  refine WP.seq (wp_upto (a := 0) (N := H.P.L) (by omega) (LI t F S V W len H.P.B H.P.L fb nbm b) ?_
    ?_ I0)
  · intro j _ hj w J
    have o_lt : oY + H.P.B * b + (H.P.B - H.P.L) + j + 1 ≤ oRsa := by
      have : H.P.B * b + H.P.B ≤ 2048 := by
        rw [← Nat.mul_succ]; exact Nat.le_trans (Nat.mul_le_mul_left _ hb) (by rw [Nat.mul_comm]; exact hnb)
      unfold oY oRsa; omega
    have hld := J.L.sld8 (d := oY + H.P.B * b + (H.P.B - H.P.L) + j) (by omega)
    have hst := J.L.sst8 (d := oY + H.P.B * b + (H.P.B - H.P.L) + j) (by omega)
    have hlj := J.L.sld8 (d := oLen + j) (by unfold oLen oRsa; omega)
    have ea₁ : off S oLen + BitVec.ofNat 64 j + BitVec.ofNat 64 0 = off S (oLen + j) := by
      rw [off_ix, off_off, Nat.add_zero]
    have ea₂ : off S (oY + H.P.B * b + (H.P.B - H.P.L)) + BitVec.ofNat 64 j + BitVec.ofNat 64 0 =
        off S (oY + H.P.B * b + (H.P.B - H.P.L) + j) := by
      rw [off_ix, off_off, Nat.add_zero]
    refine WP.mono (WP.keep [.rax, .rdi, .r9] (Q := fun w' => w'.zf = some (decide (j + 1 = H.P.L)) ∧
        w'.gpr .r9 = BitVec.ofNat 64 (j + 1) ∧
        w'.mem = w.mem.writeW (off S (oY + H.P.B * b + (H.P.B - H.P.L) + j))
          (w.mem (off S (oY + H.P.B * b + (H.P.B - H.P.L) + j)) |||
            if b = fb then w.mem (off S (oLen + j)) else 0)) ?_ rfl) fun w' ⟨⟨hz, h9, hm'⟩, hk'⟩ => ⟨hz, ?_⟩
    · xrun [ea_ix, J.rsi, J.rcx, J.r9, J.r11, ea₁, ea₂, hld, hst, hlj, mask_and, decide_eq_true_eq,
        ofNat_add_lit, VG.Proof.MlKem.X86_64.sx_ofNat (show H.P.L < 2 ^ 31 by omega),
        ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show H.P.L < 2 ^ 64 by omega)]
    · have hlv : w.mem (off S (oLen + j)) = len.getD j 0 := by
        rw [J.R.scr _ (by unfold oLen oRsa; omega), lenAt, ifn (by unfold oLen oY at *; omega)]
        exact hlen j hj
      rw [hlv, J.R.scr _ (by omega)] at hm'
      have R' := J.R.wb J.L.geo (o := oY + H.P.B * b + (H.P.B - H.P.L) + j) (by omega)
        (lenAt V len H.P.B H.P.L fb (if fb < b then H.P.L else if fb = b then j else 0)
          (oY + H.P.B * b + (H.P.B - H.P.L) + j) ||| if b = fb then len.getD j 0 else 0)
      rw [lenAt_step V len, ← hm'] at R'
      exact { J.toLRegs with
        L := J.L.of_rep J.R R' (hk'.gpr (by decide)) hk'.2.2
        keep := (J.keep.trans hk').mono (by decide)
        rcx := (hk'.gpr (by decide)).trans J.rcx, rsi := (hk'.gpr (by decide)).trans J.rsi
        rdx := (hk'.gpr (by decide)).trans J.rdx, r10 := (hk'.gpr (by decide)).trans J.r10
        r8 := (hk'.gpr (by decide)).trans J.r8, r9 := h9, r11 := (hk'.gpr (by decide)).trans J.r11, R := R' }
  · intro w J
    have hrc : off S (oY + H.P.B * b + (H.P.B - H.P.L)) + BitVec.ofNat 64 H.P.B =
        off S (oY + H.P.B * (b + 1) + (H.P.B - H.P.L)) := by
      show off (off S _) _ = _; rw [off_off, Nat.mul_succ]; congr 1; omega
    refine WP.mono (WP.keep [.rcx, .r8] (Q := fun w' => w'.zf = some (decide (b + 1 = nbm)) ∧
        w'.gpr .rcx = off S (oY + H.P.B * (b + 1) + (H.P.B - H.P.L)) ∧ w'.gpr .r8 = BitVec.ofNat 64 (b + 1) ∧
        w'.mem = w.mem) ?_ rfl) fun w' ⟨⟨hz, hc, h8, hm'⟩, hk'⟩ => ⟨hz, ?_⟩
    · xrun [J.rcx, J.r8, J.r10, VG.Proof.MlKem.X86_64.sx_ofNat (show H.P.B < 2 ^ 31 by omega), hrc,
        ofNat_add_lit, ofNat_sub_beq (show b + 1 < 2 ^ 64 by omega) (show nbm < 2 ^ 64 by omega)]
    · have R' : Rep w'.mem F S (lenAt V len H.P.B H.P.L fb (if fb < b + 1 then H.P.L else 0)) W := by
        have hc : (if fb < b then H.P.L else if fb = b then H.P.L else 0) =
            (if fb < b + 1 then H.P.L else 0) := by
          by_cases h1 : fb < b
          · rw [ifp h1, ifp (by omega)]
          · by_cases h2 : fb = b
            · rw [ifn h1, ifp h2, ifp (by omega)]
            · rw [ifn h1, ifn h2, ifn (by omega)]
        rw [hm', ← hc]; exact J.R
      exact ⟨⟨J.L.of_rep J.R R' (hk'.gpr (by decide)) hk'.2.2, (J.keep.trans hk').mono (by decide), hc,
        (hk'.gpr (by decide)).trans J.rsi, (hk'.gpr (by decide)).trans J.rdx, (hk'.gpr (by decide)).trans J.r10, h8⟩,
        R'⟩

end VG.Proof.RsaPss.X86_64

