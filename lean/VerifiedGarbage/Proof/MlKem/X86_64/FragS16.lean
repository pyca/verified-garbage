module

import VerifiedGarbage.Proof.MlKem.X86_64.FragS
public import VerifiedGarbage.Proof.MlKem.X86_64.Frag16Prim
public import VerifiedGarbage.Proof.MlKem.X86_64.FragOf
import VerifiedGarbage.Proof.MlKem.X86_64.FragL
import VerifiedGarbage.Proof.MlKem.X86_64.Rel

/-!
# ML-KEM on x86-64: `SamplePolyCBD₂` and `Â[i, j]` with 16-bit coefficients, in a layout

As `FragL.lean`'s `cbd2At_okL` and `FragS.lean`'s `sampleIJ_ok`, for
polynomials of 16-bit coefficients (512 bytes), with the working space `z`
(2048 bytes) of `vg_mlkem16_sample_ntt`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable {rbs wbs : List (Reg × Nat)}

/-! ## `SamplePolyCBD₂` -/

theorem cbd2_16At_okL {A : Arith} (hA : ArithOk A) {s : State} (L : Lay rbs wbs s) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 512 = true) :
    WP isa (cbd2_16At A p q) s fun s' => PPost s s' [(q, 512)] ∧
      PolyIsW 16 s'.mem (pa s q) (samplePolyCBD 2 (bytesAt s.mem (pa s p) 128)) :=
  cbd2_16At_ok hA hq (TwoH.of L hc)

theorem cbd2_16At_trL {A : Arith} (hA : ArithOk A) {p q : Ptr} (hq : NA q)
    (hc : twoChk (rbs ++ wbs) wbs p 128 q 512 = true) :
    RelCT isa (LRel rbs wbs) (cbd2_16At A p q) fun _ _ => True :=
  RelCT.mono (cbd2_16At_tr hA hq) (fun _ _ e => ⟨TwoH.of e.1 hc, TwoH.of e.2.1 hc, e.eq (twoChk_in hc).1,
    e.eq (twoChk_in hc).2, e.2.2.2⟩) fun _ _ _ => trivial

/-! ## `SampleNTT` of the seed at `SB` -/

/-- The checks of a call of `vg_mlkem16_sample_ntt` to `a`, with the working space `z`. -/
def samp16Chk (bs wbs : List (Reg × Nat)) (a z : Ptr) : Bool :=
  rdOk bs (sc oSB) 34 && wrOk bs wbs a 512 && wrOk bs wbs z 2048 && sepB bs (sc oSB) 34 a 512 &&
    sepB bs (sc oSB) 34 z 2048 && sepB bs a 512 z 2048

theorem samp16Chk_in {bs wbs : List (Reg × Nat)} {a z : Ptr} (hc : samp16Chk bs wbs a z = true) :
    inB bs (sc oSB) 34 = true ∧ inB bs a 512 = true ∧ inB bs z 2048 = true := by
  simp only [samp16Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨rdOk_in h1, wrOk_in h2, wrOk_in h3⟩

theorem SampH16.of {s : State} (L : Lay rbs wbs s) {a z : Ptr} (hc : samp16Chk (rbs ++ wbs) wbs a z = true) :
    SampH16 a z s := by
  simp only [samp16Chk, wrOk, rdOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨_, hrs⟩, ⟨hoa, hra⟩, hwa⟩, ⟨hoz, hrz⟩, hwz⟩, s1⟩, s2⟩, s3⟩ := hc
  exact ⟨hoa, hoz, L.disj s1, L.disj s2, L.disj s3, L.stkD hrs, L.stkD hra, L.stkD hrz, L.nwp hrz,
    covers_append (covers_cons (L.cR hrs) covers_nil) (covers_cons (L.cR hra) (covers_cons (L.cR hrz) covers_nil)),
    covers_cons (L.cW hwa) (covers_cons (L.cW hwz) covers_nil)⟩

/-- What `vg_mlkem16_sample_ntt` leaves, as `PostB`. -/
theorem SampPost16.b {a z : Ptr} {s s' : State} (h : SampPost16 a z s s') :
    PPostB s s' [(a, 512), (z, 2048)] :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by
      simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
    h.cs .rsp (by decide) (by decide), h.frame⟩

theorem sampleAt16_trL {a z : Ptr} (hna : NA a) (hnz : NA z) (hc : samp16Chk (rbs ++ wbs) wbs a z = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 34 = bytesAt y.mem (pa y (sc oSB)) 34)
      (sampleAt16 a z) fun _ _ => True :=
  RelCT.mono (sampleAt16_tr hna hnz) (fun _ _ ⟨e, hb⟩ => ⟨SampH16.of e.1 hc, SampH16.of e.2.1 hc,
    e.eq (samp16Chk_in hc).1, e.eq (samp16Chk_in hc).2.1, e.eq (samp16Chk_in hc).2.2, e.2.2.2, hb⟩)
    fun _ _ _ => trivial

/-! ## `Â[i, j]` -/

/-- The checks of `Â[i, j]`: its call, and the two bytes of the seed. -/
def ij16Chk (bs wbs : List (Reg × Nat)) (a z : Ptr) : Bool :=
  samp16Chk bs wbs a z && inB wbs (sc (oSB + 32)) 1 && inB wbs (sc (oSB + 33)) 1 &&
    keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 && keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 &&
    keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1

theorem ij16Chk_parts {bs wbs : List (Reg × Nat)} {a z : Ptr} (hc : ij16Chk bs wbs a z = true) :
    samp16Chk bs wbs a z = true ∧ inB wbs (sc (oSB + 32)) 1 = true ∧ inB wbs (sc (oSB + 33)) 1 = true ∧
      keepB bs [(sc (oSB + 32), 1)] (sc oSB) 32 = true ∧ keepB bs [(sc (oSB + 33), 1)] (sc oSB) 32 = true ∧
      keepB bs [(sc (oSB + 33), 1)] (sc (oSB + 32)) 1 = true := by
  simp only [ij16Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two indices of the seed `ρ ‖ j ‖ i`. -/
theorem setIJ16_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {i j : Nat}
    (hi : i < 256) (hj : j < 256) {a z : Ptr} (hc : ij16Chk (rbs ++ wbs) wbs a z = true) :
    WP isa (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i)) s fun s' =>
      PPost s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt s'.mem (pa s' (sc oSB)) 34 = matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j := by
  obtain ⟨_, h32, h33, k1, k2, k3⟩ := ij16Chk_parts hc
  rw [WP.block_append_iff]
  refine WP.mono (setB_okL L (by decide) hj h32) fun s₁ ⟨hP₁, hb₁⟩ => ?_
  have L₁ := L.post hP₁.b hcs
  refine WP.mono (setB_okL L₁ (by decide) hi h33) fun s₂ ⟨hP₂, hb₂⟩ => ?_
  have e1 : ∀ o, pa s₁ (sc o) = pa s (sc o) := fun o => hP₁.pa rbx_cs
  have e2 : ∀ o, pa s₂ (sc o) = pa s₁ (sc o) := fun o => hP₂.pa rbx_cs
  have hρ : bytesAt s₂.mem (pa s₂ (sc oSB)) 32 = bytesAt s.mem (pa s (sc oSB)) 32 := by
    rw [L₁.keepBytes hP₂.b k2, L.keepBytes hP₁.b k1]
  have hjb : bytesAt s₂.mem (pa s₂ (sc (oSB + 32))) 1 = [BitVec.ofNat 8 j] := by
    rw [L₁.keepBytes hP₂.b k3, e1]; exact hb₁
  have hib : bytesAt s₂.mem (pa s₂ (sc (oSB + 33))) 1 = [BitVec.ofNat 8 i] := by
    rw [e2]; exact hb₂
  refine ⟨PPost.app hP₁ hP₂ (by decide), seed_eq hρ ?_ ?_⟩
  · refine mem_of_bytesAt_one ?_; rw [← hjb, pa, pa, off_add]
  · refine mem_of_bytesAt_one ?_; rw [← hib, pa, pa, off_add]

theorem sampleIJ16_ok {s : State} (L : Lay rbs wbs s) (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a z : Ptr} (hna : NA a)
    (hnz : NA z) {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : ij16Chk (rbs ++ wbs) wbs a z = true) :
    WP isa (sampleIJ16 a i j z) s fun s' =>
      PPostB s s' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(a, 512), (z, 2048)]) ∧
      s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j)).isSome then 1 else 0)) ∧
      ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) i j) = some f →
        PolyIsW 16 s'.mem (pa s a) f := by
  unfold sampleIJ16
  rw [WP.seq_iff]
  refine WP.mono (setIJ16_ok L hcs hi hj hc) fun s₂ ⟨hP₂, hseed⟩ => ?_
  have L₂ := L.post hP₂.b hcs
  refine WP.mono (sampleAt16_ok hna hnz (SampH16.of L₂ (ij16Chk_parts hc).1)) fun s₃ h => ?_
  have hab : a.1 ∈ bases := by
    obtain ⟨n, hn, _⟩ := inB_spec (samp16Chk_in (ij16Chk_parts hc).1).2.1
    exact hcs (a.1, n) hn
  have hzb : z.1 ∈ bases := by
    obtain ⟨n, hn, _⟩ := inB_spec (samp16Chk_in (ij16Chk_parts hc).1).2.2
    exact hcs (z.1, n) hn
  have e3 : pa s₂ a = pa s a := hP₂.b.pa hab
  refine ⟨PPostB.app hP₂.b h.b (fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    exacts [hab, hzb]), ?_, fun f hf => ?_⟩
  · rw [h.r15, hseed, hP₂.cs .r15 (by decide)]
  · rw [← e3]; exact h.res f (by rw [hseed]; exact hf)

theorem sampleIJ16_tr (hcs : ∀ b ∈ rbs ++ wbs, b.1 ∈ bases) {a z : Ptr} (hna : NA a) (hnz : NA z)
    {i j : Nat} (hi : i < 256) (hj : j < 256) (hc : ij16Chk (rbs ++ wbs) wbs a z = true)
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block (setB (sc (oSB + 32)) j ++ setB (sc (oSB + 33)) i))
      (.block [])).isSome = true) :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ bytesAt x.mem (pa x (sc oSB)) 32 = bytesAt y.mem (pa y (sc oSB)) 32)
      (sampleIJ16 a i j z) fun _ _ => True := by
  have hin : inB (rbs ++ wbs) (sc oSB) 34 = true := (samp16Chk_in (ij16Chk_parts hc).1).1
  unfold sampleIJ16
  refine RelCT.seq (RelCT.postDep (taintRel [.rbx] (fun x y h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.eq hin) ht)
    (F := fun x x' => PPost x x' ([(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)]) ∧
      bytesAt x'.mem (pa x' (sc oSB)) 34 = matSeed (bytesAt x.mem (pa x (sc oSB)) 32) i j)
    (fun x y h => ⟨setIJ16_ok h.1.1 hcs hi hj hc, setIJ16_ok h.1.2.1 hcs hi hj hc⟩)
    fun x y x' y' h hx hy => ⟨h.1.post hcs hx.1.b hy.1.b, by rw [hx.2, hy.2, h.2]⟩)
    (sampleAt16_trL hna hnz (ij16Chk_parts hc).1)

end

end VG.Proof.MlKem.X86_64
