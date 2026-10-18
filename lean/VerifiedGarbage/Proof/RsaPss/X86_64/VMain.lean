module

public import VerifiedGarbage.Proof.RsaPss.X86_64.VCall
public import VerifiedGarbage.Proof.RsaPss.X86_64.Auto
public import VerifiedGarbage.Proof.RsaPss.X86_64.VFinal
public import VerifiedGarbage.Proof.RsaOaep.Mask
import VerifiedGarbage.Proof.RsaPss.EncBytes
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSASSA-PSS verification on x86-64: after the checks

`verifyMain`: the public operation writes `EM`, the accumulator of the
checks, MGF1 unmasks `DB`, the scan finds the salt, and `saltBack` hashes
it and compares the hash with `H` (`verMain_ok`): the result is
`Spec.RsaPss.verify`'s if `pre` holds the values for `n`.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Impl.RsaOaep.X86_64 (frameBytes sScr sScrLen sN sK sE sEl oEm oSt oBuf oRsa scr lay arg)
open VG.Impl.Mgf1.X86_64 (sp seqs mgfXor)
open VG.Proof.RsaOaep.X86_64 (encStack stkR fb frR frame_sub ret_sub Lay Rep Geo upd ea_sp StepW off_plus nW
  inR inR_cons inR_nil regs retR cS retR_disjoint_F wp_good block_good keep_cs3 Good Here Fns mgfXor_ok MFit
  MArgs mW mW_args mW_other mOut mOut_iff lenOf tw fnW selW)
open VG.Proof.RsaOaep (mixV srcB)
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.HashFns (StreamingOK)

/-- What a callee writing only within the ranges `rgs` of our working space,
regions `xs` apart from the frame and our working space, and the return
address below the frame leaves. -/
theorem Rep.frameX {m m' : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) {rgs : List (Nat × Nat)} (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa) {xs : List Region}
    (hx : ∀ r ∈ xs, Region.Disjoint r ⟨F, frameBytes⟩ ∧ Region.Disjoint r ⟨S, oRsa⟩)
    (hF : Frame (regs S rgs ++ xs ++ [retR F]) m m') :
    Rep m' F S (fun o => if inR rgs o then m' (off S o) else V o) W where
  scr o ho := by
    split
    · rfl
    · rename_i hn
      rw [hF _ fun r hr hc => ?_, R.scr o ho]
      rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
          apply hn
          refine ⟨p, hp, ?_⟩
          have := hrg p hp
          have := (Offset.lt_iff (off S o) S (d := p.1) (n := p.2) (by have := G.Sw; unfold oRsa at *; omega)).mp hc
          rwa [off, Mem.sub_ofNat_toNat S (by unfold oRsa at *; omega)] at this
        · exact (hx r hr).2 _ hc ((cS S (o := o) (n := 1) (by omega)).byte (by rw [BitVec.sub_self]; decide))
      · simp only [List.mem_singleton] at hr; subst hr
        exact G.dRS' ho hc
  fr k hk := by
    rw [Bignum.word, hF.readW (r := ⟨off F (8 * k), 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
    · exact R.fr k hk
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
        exact Region.Disjoint.sub_left (Region.Disjoint.sub_right G.dFS (Offset.sub_base S (hrg p hp)))
          (Offset.sub_base F (by unfold nW frameBytes at *; omega))
      · exact ((hx r hr).1.symm.sub_left (Offset.sub_base F (by unfold nW frameBytes at *; omega)))
    · simp only [List.mem_singleton] at hr; subst hr
      exact retR_disjoint_F F hk

theorem fnz_lt (f : Nat → Byte) : ∀ {j i : Nat}, fnz f j = some i → i < j
  | 0, _, h => by simp [fnz] at h
  | j + 1, i, h => by
    simp only [fnz] at h
    split at h
    · rename_i i' hi'; cases h; have := fnz_lt f hi'; omega
    · split at h
      · cases h
      · cases h; omega

theorem fnz_getD_lt (f : Nat → Byte) {j : Nat} (hj : 1 ≤ j) : (fnz f j).getD 0 < j := by
  cases h : fnz f j with
  | none => simp; omega
  | some i => simp; exact fnz_lt f h

theorem written_getD {m : Mem} {p : Addr} {n : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (h : Spec.Rsa.written m p n r o) : ∀ i < n, m (p + BitVec.ofNat 64 i) = (o.getD (Spec.RsaPss.zeros n)).getD i 0 := by
  intro i hi
  have hb : Spec.Rsa.bytesAt m p n = o.getD (Spec.RsaPss.zeros n) := by
    cases o with
    | none => exact h.2
    | some y => exact h.2
  rw [← hb, Spec.Rsa.bytesAt, getD_map_range' hi]

theorem posScan_good : Good posScan := ⟨rfl, rfl, by decide⟩
theorem posCheck_good : Good posCheck := ⟨rfl, rfl, by decide⟩
theorem saltBack_good : Good saltBack := ⟨rfl, rfl, by decide⟩

variable {s : State}

/-- The words of `vcW` that `verifyMain` keeps. -/
def vKs : List Nat := [14, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 37, 38, 39, 40, 41, 42, 43, 45, 46, 47, 48,
  49, 50]

theorem vKs_iff {k : Nat} (h : k ∈ vKs) : k = 14 ∨ (21 ≤ k ∧ k ≤ 31) ∨ (37 ≤ k ∧ k ≤ 43) ∨ (45 ≤ k ∧ k ≤ 50) := by
  simp only [vKs, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- The slots of `vcW` the rest of `verifyMain` reads. -/
def ArgsV (s : State) (W : Nat → BitVec 64) : Prop := ∀ k ∈ vKs, W k = vcW s k

theorem ArgsV.upd' {W : Nat → BitVec 64} (h : ArgsV s W) {j : Nat} (hj : j < 14 ∨ (31 < j ∧ j < 37) ∨ j = 44 ∨
    (14 < j ∧ j < 21)) (v : BitVec 64) : ArgsV s (upd W j v) := fun k hk => by
  have := vKs_iff hk
  rw [show upd W j v k = W k from ifn (by omega) _ _]; exact h k hk

theorem ArgsV.mW {W : Nat → BitVec 64} (h : ArgsV s W) (S : Addr) (a b c d : Nat) : ArgsV s (mW W S a b c d) :=
  fun k hk => by have := vKs_iff hk; rw [mW_other (by omega)]; exact h k hk

theorem ArgsV.w {W : Nat → BitVec 64} (h : ArgsV s W) :
    W 21 = stackArg s 0 ∧ W 22 = s.gpr .rdi ∧ W 23 = s.gpr .rsi ∧ W 24 = s.gpr .rdx ∧ W 25 = s.gpr .rcx ∧
    W 26 = stackArg s 5 ∧ W 27 = s.gpr .r8 ∧ W 28 = (if vfixed s then 0 else 1) ∧ W 29 = stackArg s 3 ∧
    W 30 = maskV (n0v s) ∧ W 31 = BitVec.ofNat 64 (loV (n0v s)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by decide)]; simp [vcW, verW, fnW, selW, verPW, upd])

theorem ArgsV.sel {W : Nat → BitVec 64} (h : ArgsV s W) :
    W 39 = BitVec.ofNat 64 (lenOf (vselH s)) ∧ W 43 = BitVec.ofNat 64 (lenOf (vselG s)) ∧
    (W 45 = tw s.mem (vtabH s) 0 ∧ W 46 = tw s.mem (vtabH s) 1 ∧ W 47 = tw s.mem (vtabH s) 2) ∧
    (W 48 = tw s.mem (vtabG s) 0 ∧ W 49 = tw s.mem (vtabG s) 1 ∧ W 50 = tw s.mem (vtabG s) 2) := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    (rw [h _ (by decide)]; simp [vcW, verW, fnW, selW, upd])

/-- The streaming functions of the table `j` (10 or 11) of the entry `s`. -/
abbrev VFns (s : State) (T : Spec.HashFns.Streaming) (j : Nat) : Prop :=
  Fns encStack s T (tw s.mem (stackArg s j) 0) (tw s.mem (stackArg s j) 1) (tw s.mem (stackArg s j) 2)

variable {TH TG : Spec.HashFns.Streaming} {Hh Gh : Spec.Mgf1.Hash} (hTH : StreamingOK TH Hh)
  (hTG : StreamingOK TG Gh)

include hTH hTG in
theorem verMain_ok (v : PublicImpl) (hp : VPre s) (fH : VFns s TH 10) (fG : VFns s TG 11)
    (eH : Spec.HashId.mgf1 (vselH s) = some Hh) (eG : Spec.HashId.mgf1 (vselG s) = some Gh) {t : State}
    (he : VEnv s t) (L : Lay t (fb s) (stackArg s 4))
    (R : Rep t.mem (fb s) (stackArg s 4) (fun o => s.mem (off (stackArg s 4) o)) (vcW s))
    (hax : t.gpr .rax = BitVec.ofNat 64 (vk s - loV (n0v s) - (lenOf (vselH s) + 2))) (hn0 : n0v s ≠ 0)
    (hfit : lenOf (vselH s) + 2 + vsl s ≤ vk s - loV (n0v s)) :
    WP isa (verifyMain v.name v.code) t fun t' => VEnv s t' ∧ (VConsistent s → t'.gpr .rax =
      if Spec.RsaPss.verify Hh Gh (Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r8) Hh.len)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
        (Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32)) then 1 else 0) := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hDH : TH.S.digestBytes = lenOf (vselH s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTH eH
  have hDG : TG.S.digestBytes = lenOf (vselG s) := VG.Proof.RsaOaep.X86_64.lenOf_eq hTG eG
  obtain ⟨-, hzF, -, hzDF, hzD⟩ := VG.Proof.RsaOaep.X86_64.sizes hTH
  have hlo := loV_le (n0v s)
  have c1 : oEm = 0 := rfl
  have c2 : oSt = 3072 := rfl
  have c3 : oBuf = 1024 := rfl
  have c5 : oRsa = 8192 := rfl
  generalize hD : lenOf (vselH s) = D at *
  generalize hlo' : loV (n0v s) = lo at *
  generalize hk : vk s = k at *
  have hk' : (s.gpr .rsi).toNat = k := hk
  have hA0 : ArgsV s (vcW s) := fun _ _ => rfl
  obtain ⟨w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31⟩ := hA0.w
  rw [hlo'] at w31
  unfold verifyMain seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `dbLen` and `DB`.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (dbSlots_ok L R w31 hax))
    fun t1 ⟨⟨L1, k1, R1⟩, sp1, mx1, f1⟩ => ?_)
  have he1 := he.step k1.2.1 k1.2.2 sp1 (keep_cs3 k1 (by decide)) mx1 f1
  have hA1 : ArgsV s (upd (upd (vcW s) 44 (BitVec.ofNat 64 (k - lo - (D + 2) + 1))) 33
      (off (stackArg s 4) (oEm + lo))) := (hA0.upd' (j := 44) (by omega) _).upd' (j := 33) (by omega) _
  -- The public operation.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (pubArgsV_ok hp L1 he1.rd he1.fr R1
      (by rw [hA1 21 (by decide)]; exact w21) (by rw [hA1 23 (by decide)]; exact w23)
      (by rw [hA1 24 (by decide)]; exact w24) (by rw [hA1 25 (by decide)]; exact w25)
      (by rw [hA1 26 (by decide)]; exact w26)))
    fun t2 ⟨⟨L2, k2, R2, hdi, hsi, hdx, hcx, h8, h9⟩, sp2, mx2, f2⟩ => ?_)
  have he2 := he1.step k2.2.1 k2.2.2 sp2 (keep_cs3 k2 (by decide)) mx2 f2
  refine WP.seq (WP.mono (callV_ok v hp L2 R2 he2.rd he2.wr he2.fr (by simp [upd]) (by simp [upd])
    (by simp [upd]) (by simp [upd]) hdi hsi hdx hcx h8 h9)
    fun t3 ⟨hout, rd3, wr3, cs3, mx3, f3, fr3⟩ => ?_)
  have he3 := he2.step rd3 wr3 (cs3 .rsp (by decide)) (fun r hr _ => cs3 r hr) mx3 f3
  have G' := L2.geo
  have ⟨r1, r2⟩ := rsaV_toNat hp
  have hsl' := hp.hsl'
  have hfr3 : Frame (regs (stackArg s 4) [(oEm, k)] ++ [rsaRV s] ++ [retR (fb s)]) t2.mem t3.mem :=
    fr3.sub fun r hr => by
      simp only [callWrV, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨off (stackArg s 4) oEm, k⟩, by simp [regs], by simp only [emRV, hk']; exact fun _ h => h⟩
      · exact ⟨rsaRV s, by simp, fun _ h => h⟩
      · exact ⟨retR (fb s), by simp,
          Offset.sub_below (fb s) (a := 8) (n := 8) (b := 16) (m := 16) (by decide) (by decide)⟩
  have hx : ∀ r ∈ [rsaRV s], Region.Disjoint r ⟨fb s, frameBytes⟩ ∧ Region.Disjoint r ⟨stackArg s 4, oRsa⟩ :=
    fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine ⟨(hp.dKS.symm.sub_left (rsaV_sub hp)).sub_right (frame_sub s), ?_⟩
      have := Offset.disjoint (stackArg s 4) (d := oRsa) (n := (stackArg s 5 - 1024).toNat * 8) (e := 0) (k := oRsa)
        (.inr (by omega)) (by rw [r1]; have := hp.wS; unfold oRsa; omega) (by decide)
      rwa [BitVec.add_zero] at this
  have R3 := Rep.frameX G' R2 (rgs := [(oEm, k)]) (by simp; omega) hx hfr3
  have L3 : Lay t3 (fb s) (stackArg s 4) := L2.congr (cs3 .rsp (by decide)) wr3 (by
    rw [VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl, VG.Proof.RsaOaep.X86_64.slot_eq sScr 14 rfl,
      R3.fr 14 (by decide), R2.fr 14 (by decide)])
  obtain ⟨V3, R3, hV3a, hV3b⟩ := VG.Proof.RsaOaep.X86_64.Rep.ex R3
  have hV3 : ∀ o, ¬ (oEm ≤ o ∧ o < oEm + k) → V3 o = s.mem (off (stackArg s 4) o) := fun o ho =>
    hV3a o (by simp only [inR_cons, inR_nil, or_false]; exact ho)
  have hA2 : ArgsV s (upd (upd (upd (upd (upd (upd (vcW s) 44 (BitVec.ofNat 64 (k - lo - (D + 2) + 1))) 33
      (off (stackArg s 4) (oEm + lo))) 0 (stackArg s 0)) 1 (s.gpr .rsi)) 2 (off (stackArg s 4) oRsa)) 3
      (stackArg s 5 - 1024)) :=
    (((hA1.upd' (j := 0) (by omega) _).upd' (j := 1) (by omega) _).upd' (j := 2) (by omega) _).upd' (j := 3)
      (by omega) _
  -- The accumulator.
  have hc8 := maskV_byte (show n0v s < 256 from (s.mem (s.gpr .rdi)).isLt)
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (acc0_ok L3 R3 (k := k) (lo := lo)
      (c := (maskV (n0v s)).setWidth 8)
      (by rw [hA2 23 (by decide), w23, ← hk', BitVec.ofNat_toNat, BitVec.setWidth_eq]) (by simp [upd])
      (by rw [hA2 30 (by decide), w30]; exact hc8) (by rw [hA2 31 (by decide)]; exact w31) (by omega) (by omega)
      (by omega)))
    fun t4 ⟨⟨L4, k4, R4⟩, sp4, mx4, f4⟩ => ?_)
  have he4 := he3.step k4.2.1 k4.2.2 sp4 (keep_cs3 k4 (by decide)) mx4 f4
  have hA4 := hA2.upd' (j := 4) (by omega) (acc0V (V3 (oEm + k - 1)) (V3 oEm) (V3 (oEm + lo))
    ((maskV (n0v s)).setWidth 8) lo)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -⟩ := hA4.w
  obtain ⟨-, -, -, -⟩ := hA4.sel
  -- MGF1.
  generalize hdb : k - lo - (D + 2) + 1 = db at *
  have hdb1 : 1 ≤ db := by omega
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (mgfArgs_ok L4 R4 (e := oEm + lo) (db := db) (D := D)
      (by simp [upd]) (by simp [upd]) (by rw [hA4 39 (by decide)]; exact hA0.sel.1.trans (by rw [hD]))))
    fun t5 ⟨⟨L5, k5, R5⟩, sp5, mx5, f5⟩ => ?_)
  have he5 := he4.step k5.2.1 k5.2.2 sp5 (keep_cs3 k5 (by decide)) mx5 f5
  have hA5 := hA4.mW (stackArg s 4) (oEm + lo + db) D (oEm + lo) db
  obtain ⟨-, -, -, ⟨g0, g1, g2⟩⟩ := hA5.sel
  refine WP.seq (WP.mono (wp_good VG.Proof.RsaOaep.X86_64.mgfXor_good (mgfXor_ok hTG fG (Gs := Gh)
      (fun x => by rw [hTG.hash]) hTG.len hTG.valid he5.here L5 R5
      (src := oEm + lo + db) (srcLen := D) (dst := oEm + lo) (dstLen := db)
      ⟨by omega, by omega, .inr (by omega), hdb1, by omega⟩ (mW_args _ _ _ _ _ _) ⟨g0, g1, g2⟩
      (by rw [hA5 43 (by decide), hA0.sel.2.1, hDG])))
    fun t6 ⟨⟨L6, _, rd6, wr6, cs6, V6, W6, R6, hW6, hV6⟩, sp6, mx6, f6⟩ => ?_)
  have he6 := he5.step rd6 wr6 sp6 (fun r hr _ => cs6 r hr) mx6 f6
  have hA6 : ArgsV s W6 := fun j hj => (hW6 j (by have := vKs_iff hj; unfold nW frameBytes; omega)
    (by have := vKs_iff hj; omega) (by have := vKs_iff hj; omega)).trans (hA5 j hj)
  have w6_33 : W6 33 = off (stackArg s 4) (oEm + lo) := (hW6 33 (by decide) (by decide) (by decide)).trans
    (by rw [mW_other (by omega)]; simp [upd])
  have w6_44 : W6 44 = BitVec.ofNat 64 db := (hW6 44 (by decide) (by decide) (by decide)).trans
    (by rw [mW_other (by omega)]; simp [upd])
  have w6_4 : W6 4 = acc0V (V3 (oEm + k - 1)) (V3 oEm) (V3 (oEm + lo)) ((maskV (n0v s)).setWidth 8) lo :=
    (hW6 4 (by decide) (by decide) (by decide)).trans (by rw [mW_other (by omega)]; simp [upd])
  obtain ⟨-, -, -, -, -, -, x27, x28, x29, x30, -⟩ := hA6.w
  -- The top bits of `DB`.
  refine WP.seq (WP.mono (wp_good (block_good _ rfl rfl) (clearTop_ok L6 R6 (c := (maskV (n0v s)).setWidth 8) w6_33 (by rw [x30]; exact hc8)
      (by omega)))
    fun t7 ⟨⟨L7, k7, R7⟩, sp7, mx7, f7⟩ => ?_)
  have he7 := he6.step k7.2.1 k7.2.2 sp7 (keep_cs3 k7 (by decide)) mx7 f7
  -- The salt.
  refine WP.seq (WP.mono (wp_good posScan_good (posScan_ok L7 R7 w6_33 w6_44 hdb1 (by omega)))
    fun t8 ⟨⟨k8, hm8, hdx8, hsi8, h118⟩, sp8, mx8, f8⟩ => ?_)
  have he8 := he7.step k8.2.1 k8.2.2 sp8 (keep_cs3 k8 (by decide)) mx8 f8
  have L8 : Lay t8 (fb s) (stackArg s 4) := L7.congr (k8.gpr (by decide)) k8.2.2 (by rw [hm8])
  have R8 := hm8 ▸ R7
  set f := fun i => upd V6 (oEm + lo) (V6 (oEm + lo) &&& (maskV (n0v s)).setWidth 8) (oEm + lo + i) with hf
  have hpos := fnz_getD_lt f hdb1
  refine WP.seq (WP.mono (wp_good posCheck_good (posCheck_ok L8 R8 (fixed := vfixed s) w6_44 x28 hpos hdx8 hsi8
      h118))
    fun t9 ⟨⟨L9, k9, R9⟩, sp9, mx9, f9⟩ => ?_)
  have he9 := he8.step k9.2.1 k9.2.2 sp9 (keep_cs3 k9 (by decide)) mx9 f9
  set pos := (fnz f db).getD 0 with hposd
  have hA9 : ArgsV s _ := ((hA6.upd' (j := 32) (by omega) (BitVec.ofNat 64 pos)).upd' (j := 4) (by omega)
    (acc1V (W6 4) (fnz f db).isSome (((fnz f db).map f).getD 0) (vfixed s) (BitVec.ofNat 64 (db - pos - 1))
      (W6 29))).upd' (j := 5) (by omega) (BitVec.ofNat 64 (db - pos - 1))
  obtain ⟨-, -, -, -, -, -, y27, y28, y29, -, -⟩ := hA9.w
  obtain ⟨y39, -, ⟨y45, y46, y47⟩, -⟩ := hA9.sel
  have hr9 : (s.gpr .r9).toNat = D := by rw [hp.dl Hh eH, hTH.len, hDH]
  have hsl1 : vfixed s = true → (stackArg s 3).toNat ≤ db := fun hf' => by
    have : vsl s = (stackArg s 3).toNat := by unfold vsl; rw [ifp hf']
    omega
  refine WP.mono (wp_good saltBack_good (saltBack_ok hTH fH (Hs := Hh) (fun x => by rw [hTH.hash]) he9.here L9 R9
      (D := D) (e := oEm + lo) (db := db) (pos := pos) (ln := db - pos - 1) (sl := (stackArg s 3).toNat)
      (fixed := vfixed s) (p := s.gpr .r8)
      (by rw [y39, hD]) hDH ⟨y45, y46, y47⟩ y27 (by simp [upd, w6_33]) (by simp [upd, w6_44])
      (by simp [upd]) (by simp [upd]) (by omega) y28
      (by rw [y29, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hsl1
      (fun hf' h4 => by
        simp only [upd, Nat.reduceEqDiff, ite_false, ite_true] at h4
        have := ((acc1V_eq_zero _ _ _ _ _ _).mp h4).2.2.2 hf'
        rw [x29] at this
        have hl : db - pos - 1 < 2 ^ 64 := by omega
        rw [ofNat_eq_iff hl] at this
        omega)
      (by omega)
      (fun i hi => by
        rw [he9.rd, hp.hrd]
        exact ⟨dgR s, List.mem_append_left _ (by simp [vrd]),
          Offset.contains_base _ (by rw [hr9]; omega) (by omega)⟩)
      (fun i hi j hj => VG.Proof.RsaOaep.X86_64.ne_of_disjoint hp.ddS
        (Offset.contains_base _ (by rw [hr9]; omega) (by omega))
        (Offset.contains_base _ (by have := hp.hsl'; unfold oMp; omega) (by unfold oMp; omega)))))
    fun t10 ⟨⟨L10, hh10, rd10, wr10, cs10, hax10⟩, sp10, mx10, f10⟩ => ?_
  refine ⟨he9.step rd10 wr10 sp10 (fun r hr _ => cs10 r hr) mx10 f10, fun hq => ?_⟩
  rw [hax10]
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hnB := bytesAt_cons s.mem (s.gpr .rdi) k'
  rw [← hk'] at hnB
  rw [hnB]
  have hlen : ((List.range k').map fun i => s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1))).length = k' := by simp
  have hn0' : s.mem (s.gpr .rdi) ≠ 0 := fun h => hn0 (by unfold n0v; rw [h]; rfl)
  have hEM := written_getD (hout hq)
  rw [hnB] at hEM
  have hdig : (List.range D).map (fun i => t9.mem (s.gpr .r8 + BitVec.ofNat 64 i)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .r8) Hh.len := by
    rw [hTH.len, hDH]
    have := FrV.bytes he9.fr (p := s.gpr .r8) (len := D) (by rw [← hr9]; exact hp.dKd)
      (by rw [← hr9]; exact hp.ddS.symm) (by omega)
    exact this
  have hsl : Spec.RsaPss.expectedSaltLen (stackArg s 3) ((stackArg s 2).setWidth 32) =
      if vfixed s then some (stackArg s 3).toNat else none := by
    unfold Spec.RsaPss.expectedSaltLen vfixed
    by_cases h : (stackArg s 2).setWidth 32 = 0
    · rw [ifp h, decide_eq_true h]; rfl
    · rw [ifn h, decide_eq_false h]; rfl
  rw [hsl]
  have hiff := vfinal hTH.valid hTG.valid (n₀ := s.mem (s.gpr .rdi))
    (rest := (List.range k').map fun i => s.mem (s.gpr .rdi + BitVec.ofNat 64 (i + 1)))
    (eB := Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    (sB := Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
    (mHash := Spec.Rsa.bytesAt s.mem (s.gpr .r8) Hh.len) (D := D) (lo := lo) (db := db) (fixed := vfixed s)
    (slen := stackArg s 3) (V3 := V3) (V6 := V6) hn0' (by rw [hlen]; omega) (by rw [hlen]; omega)
    (by rw [← hlo']) (by simp [Spec.Rsa.bytesAt, hk', hlen]) (by simp [Spec.Rsa.bytesAt])
    (by rw [hTH.len, hDH]) (by rw [hlen]; omega) (by rw [hlen]; unfold vsl at hfit; exact hfit)
    (fun i hi => by
      rw [hV3b _ (by simp only [inR_cons, inR_nil, or_false]; rw [hlen] at hi; omega), ← off_plus]
      rw [hlen] at hi ⊢
      have := hEM i (by rw [hk']; exact hi)
      rwa [show Spec.RsaPss.zeros (s.gpr .rsi).toNat = Spec.RsaPss.zeros (k' + 1) by rw [hk']] at this)
    (fun o ho => hV6 o (by omega) ((mOut_iff _).mpr (.inl ho)))
  rw [hlen] at hiff
  have e1 : ∀ i, oEm + lo + pos + 1 + i = oEm + lo + (pos + 1 + i) := fun i => by omega
  have e2 : ∀ i, oEm + lo + db + i = oEm + lo + (db + i) := fun i => by omega
  simp only [e1, e2, hdig] at ⊢
  have hcond : (upd (upd (upd W6 32 (BitVec.ofNat 64 ((fnz f db).getD 0))) 4
      (acc1V (W6 4) (fnz f db).isSome (((fnz f db).map f).getD 0) (vfixed s)
        (BitVec.ofNat 64 (db - (fnz f db).getD 0 - 1)) (W6 29))) 5
      (BitVec.ofNat 64 (db - (fnz f db).getD 0 - 1))) 4 =
      acc1V (W6 4) (fnz f db).isSome (((fnz f db).map f).getD 0) (vfixed s)
        (BitVec.ofNat 64 (db - (fnz f db).getD 0 - 1)) (W6 29) := by simp [upd]
  rw [hcond, w6_4, x29]
  split
  · rename_i h1
    rw [ite_eq_left (hiff.mp h1)]
  · rename_i h1
    rw [ite_eq_right (fun h' => h1 (hiff.mpr h'))]

end VG.Proof.RsaPss.X86_64
