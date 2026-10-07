import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall

/-!
# RSASSA-PSS signing on AArch64: after the checks

`main_ok`: from the checks passed (`AtMain`), the encoding into `EM`
(`signEnc_ok`), the call's arguments and the call: `out` holds the private
operation on the encoding.
-/

namespace VG.Proof.RsaPss.AArch64.Sgn

open VG VG.AArch64 VG.Impl.RsaPss.AArch64 VG.WriteBytes
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.RsaPkcs1Sig.AArch64 (PrivChecked)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.RsaPss.AArch64 (off off_add Lay mgfWr slotR signEnc_ok)

/-- After the checks, with `lo` and the mask `c` in their slots and
`emLen - hLen - 2` in `x9`. -/
structure AtMain (D : Nat) (s : State) (lo : Nat) (c : Byte) (w : State) : Prop where
  sp : w.sp = fb s
  rd : w.rd = s.rd
  wr : w.wr = ⟨fb s, frameBytes⟩ :: s.wr
  x9 : w.gpr .x9 = BitVec.ofNat 64 ((s.gpr .x3).toNat - lo - (D + 2))
  x19 : w.gpr .x19 = off (scr s) oSt
  x20 : w.gpr .x20 = scr s
  x21 : w.gpr .x21 = off (scr s) oDig
  x23 : w.gpr .x23 = s.gpr .x3
  v : ∀ r ∈ preservedV, (w.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  mem : Frame [⟨fb s, frameBytes⟩] s.mem w.mem
  fr : Fr s w.mem
  lo : w.mem.readW (fb s + BitVec.ofNat 64 sLo) 64 = BitVec.ofNat 64 lo
  c : w.mem.readW (fb s + BitVec.ofNat 64 sC) 64 = BitVec.setWidth 64 c

/-- The digest and the salt, as the entry state gives them. -/
abbrev digB (D : Nat) (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 8) D
abbrev saltB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 10).toNat

/-- The encoding `signEnc` writes, from the entry state. -/
def encEm (G : Spec.Mgf1.Hash) (D : Nat) (s : State) (lo : Nat) (c : Byte) : List Byte :=
  (List.range (s.gpr .x3).toNat).map (RsaPss.emT lo ((s.gpr .x3).toNat - lo - D - 1) (stackArg s 10).toNat (saltB s)
    (G.hash (Spec.RsaPss.zeros 8 ++ digB D s ++ saltB s))
    (Spec.Mgf1.mgf1 G (G.hash (Spec.RsaPss.zeros 8 ++ digB D s ++ saltB s)) ((s.gpr .x3).toNat - lo - D - 1)) c)

theorem mgfWr_sub (s : State) {K : Nat} (hK : 16 ≤ K) :
    ∀ r ∈ mgfWr (fb s) (scr s), r = ⟨scr s, oRsa⟩ ∨ Region.Sub r (kR K s) := by
  intro r hr
  simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)
  · exact .inr (frame_sub K s (by decide))
  · exact .inr (frame_sub K s (by decide))

theorem rsa_sub {D K : Nat} {s : State} (hp : PreS D K s) : Region.Sub ⟨scr s, oRsa⟩ (sR s) :=
  Region.sub_prefix (by have := hp.hs; unfold oRsa; omega)

/-- A buffer apart from the stack and the working space is apart from what
`mgfXor` and the encoding write. -/
theorem mgfWr_disj {D K : Nat} {s : State} (hp : PreS D K s) (hK : 16 ≤ K) {R : Region}
    (hk : (kR K s).Disjoint R) (hs : R.Disjoint (sR s)) : ∀ r ∈ mgfWr (fb s) (scr s), R.Disjoint r := by
  intro r hr
  rcases mgfWr_sub s hK r hr with rfl | h
  · exact hs.sub_right (rsa_sub hp)
  · exact (hk.sub_left h).symm

/-- The encoding: `EM` holds `encEm`. -/
theorem enc_ok {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
    (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) {K : Nat} {s w : State}
    (hp : PreS H.D K s) (hK : 16 ≤ K) {lo : Nat} {cb : Byte}
    (hm : AtMain H.D s lo cb w) (hlo : lo ≤ 1)
    (hfit : H.D + (stackArg s 10).toNat + 2 ≤ (s.gpr .x3).toNat - lo) :
    WP isa (signEnc H) w (Main s (encEm G H.D s lo cb)) := by
  have hk2 := hp.k2
  have hfb := fb_toNat hp
  have hws : (scr s).toNat + (stackArg s 12).toNat * 8 ≤ 2 ^ 64 := hp.ws
  have hhs := hp.hs
  have L : Lay w (fb s) (scr s) := {
    sp := hm.sp
    x20 := hm.x20
    fw := by rw [hm.wr]; exact List.mem_cons_self
    sw := ⟨sR s, by rw [hm.wr]; exact List.mem_cons_of_mem _ hp.hws,
      ⟨rfl, show oRsa ≤ (stackArg s 12).toNat * 8 by unfold oRsa; omega⟩⟩
    Fw := by omega
    Sw := by unfold oRsa; omega
    dFS := (hp.ks.sub_left (frame_sub0 K s)).sub_right (rsa_sub hp)
    dB := (hp.ks.sub_left fun a h => below_sub K s a
      (Offset.sub_below (fb s) (a := 16) (b := K) (n := 16) (m := K) hK (by omega) a h)).sub_right (rsa_sub hp) }
  have hdR : ∀ j < H.D, InRegions (w.rd ++ w.wr) (stackArg s 8 + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [hm.rd, hm.wr]
    exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
      ⟨dgR H.D s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wdg; omega)⟩
  have hqR : ∀ j < (stackArg s 10).toNat, InRegions (w.rd ++ w.wr) (stackArg s 9 + BitVec.ofNat 64 j) 1 :=
    fun j hj => by
      rw [hm.rd, hm.wr]
      exact Covers.left (Covers.trans (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; simp) hp.hrd) _ _
        ⟨slR s, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by have := hp.wsl; omega)⟩
  have hbd : Spec.Rsa.bytesAt w.mem (stackArg s 8) H.D = digB H.D s :=
    VG.Proof.RsaPkcs1Sig.bytes_apart (R := dgR H.D s) hm.mem (hp.kdg.sub_left (frame_sub0 K s)).symm
      (by have := hp.wdg; dsimp only; omega)
  have hbs : Spec.Rsa.bytesAt w.mem (stackArg s 9) (stackArg s 10).toNat = saltB s :=
    VG.Proof.RsaPkcs1Sig.bytes_apart (R := slR s) hm.mem (hp.ksl.sub_left (frame_sub0 K s)).symm
      (by have := hp.wsl; dsimp only; omega)
  refine WP.mono (signEnc_ok hH hGh hGl hG L (fun _ _ => rfl) (k := (s.gpr .x3).toNat) (lo := lo)
    (sl := (stackArg s 10).toNat) (c := cb) (dig := stackArg s 8) (q := stackArg s 9) hm.x19 hm.x21
    (by rw [hm.x23, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hm.x9 hm.lo hm.c hm.fr.dig hm.fr.salt
    (by rw [hm.fr.sl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hk2 hlo hfit hdR
    (mgfWr_disj hp hK hp.kdg hp.dgs) hqR (mgfWr_disj hp hK hp.ksl hp.sls))
    fun t ⟨sp', rd', wr', cs', v', fr', em'⟩ => ?_
  rw [hbd, hbs] at em'
  exact {
    sp := sp'.trans hm.sp
    rd := rd'.trans hm.rd
    wr := wr'.trans hm.wr
    x20 := (cs' .x20 (by decide)).trans hm.x20
    x23 := (cs' .x23 (by decide)).trans hm.x23
    v := fun r hr => (v' r hr).trans (hm.v r hr)
    mem := (hm.mem.mono (by simp)).trans (fr'.sub fun r hr => by
      simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨sR s, by simp, rsa_sub hp⟩
      · exact ⟨below (fb s) 16, by simp, fun _ h => h⟩
      · exact ⟨⟨fb s, frameBytes⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨⟨fb s, frameBytes⟩, by simp, Offset.sub_base _ (by decide)⟩)
    fr := hm.fr.frame fr' (fun r hr => by
        simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hp.ks.sub_left (frame_sub K s (d := 96) (n := 152) (by decide))).sub_right (rsa_sub hp)
        · exact Offset.disjoint_below _ (by omega)
        · exact Offset.disjoint _ (by decide) (by decide) (by decide)
        · exact Offset.disjoint _ (by decide) (by decide) (by decide))
      (fun r hr => by
        simp only [mgfWr, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hp.ks.sub_left (frame_sub K s (d := 288) (n := 16) (by decide))).sub_right (rsa_sub hp)
        · exact Offset.disjoint_below _ (by omega)
        · exact Offset.disjoint _ (by decide) (by decide) (by decide)
        · exact Offset.disjoint _ (by decide) (by decide) (by decide))
    em := by
      simp only [Spec.Rsa.bytesAt, encEm]
      refine List.map_congr_left fun i hi => ?_
      rw [off_add]
      exact em' i (List.mem_range.mp hi) }

theorem main_ok {H : Hash} (hH : HashOK H) {G : Spec.Mgf1.Hash} (hGh : ∀ x, G.hash x = hH.SH.H.hash x)
    (hGl : G.len = H.D) (hG : Proof.Mgf1.Valid G) (c : PrivChecked) {K : Nat} {s w : State}
    (hp : PreS H.D K s) (hK : 16 ≤ K) (hcK : c.stack ≤ K) {lo : Nat} {cb : Byte}
    (hm : AtMain H.D s lo cb w) (hlo : lo ≤ 1)
    (hfit : H.D + (stackArg s 10).toNat + 2 ≤ (s.gpr .x3).toNat - lo) :
    WP isa (signMain H c.name c.code) w fun t => Mid s t ∧
      Spec.Rsa.writtenOutcome t.mem (s.gpr .x0) (s.gpr .x3).toNat ((t.gpr .x0).setWidth 32)
        (privOut s (encEm G H.D s lo cb)) := by
  unfold signMain seqs seqs seqs
  refine WP.seq (WP.mono (enc_ok hH hGh hGl hG hp hK hm hlo hfit) fun t hM => ?_)
  refine WP.seq (WP.mono (privArgs_ok hp hK hM) fun u hu => ?_)
  exact WP.mono (call_ok c hp hK hcK hu) fun t' ht' => ⟨ht'.toMid, ht'.res⟩

end VG.Proof.RsaPss.AArch64.Sgn
