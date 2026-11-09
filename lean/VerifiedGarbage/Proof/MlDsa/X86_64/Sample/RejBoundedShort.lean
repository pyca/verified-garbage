module
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBounded

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStream
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejBoundedLoop
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejBounded
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: the prefix loop proofs cost more to check than their imports.

/-!
# ML-DSA on x86-64: the two-block rejection-sampling prefix

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ, 272)` (`J6`), the branch on `η`, and the loop for `η`, iteration `t` of
which starts from `LAt σ pos t` with the coefficients `rbFold` samples from the
first `t` bytes of output stored.
-/

@[expose] public section

namespace VG
materialize_code Impl.MlDsa.X86_64.Sample.rejBoundedShort
end VG

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

namespace RejBoundedShort

/-- The call. -/
abbrev spOf (σ : State) (pos : BitVec 64) : Sp := {RejBounded.spOf σ with prm := pos}

abbrev spInit (σ : State) : Sp := {RejBounded.spOf σ with prm := σ.gpr .r12}

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 66

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := H (B σ) 272

section
variable {σ : State} {pos : BitVec 64} (hp : rbK.pre σ)
include hp

theorem spOk : SpOk (spOf σ pos) σ := SpongeStream.sp_param (RejBounded.spOk hp) pos

theorem initOk : SpOk (spInit σ) σ := SpongeStream.sp_param (RejBounded.spOk hp) (σ.gpr .r12)

theorem eta : etaOf σ = 2 ∨ etaOf σ = 4 := hp.2.2.2.2.2.2.2.2.2.2.2.2

omit hp in
theorem sx66 : BitVec.signExtend 64 (66 : BitVec 32) = BitVec.ofNat 64 66 := by decide

theorem pro_ok : WP isa (.block rbShortPro) σ (J0 (spInit σ) σ) := by
  have hsp := initOk hp
  refine WP.mono (WP.keep [.rbx, .rbp, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spInit σ).at' 2024) (σ.gpr .rbx)).writeW ((spInit σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spInit σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdx ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 66)
    (by unfold rbShortPro; xrun [inScrσ hsp (a := 2024) (n := 8) (by decide),
      inScrσ hsp (a := 2032) (n := 8) (by decide), inScrσ hsp (a := 2040) (n := 8) (by decide), sx66])
    (by decide)) fun s ⟨⟨hm, hb, hp, hc, h8⟩, hk⟩ =>
      pro_J0 hm hb hp (hk.gpr (by decide)) hc h8 (hk.mono (by decide))

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rbFold (etaOf σ) [] ((X σ).take t)

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (pos : BitVec 64) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ pos) σ s
  out : bytesAt s.mem ((spOf σ pos).at' 840) 272 = X σ
  rsi : s.gpr .rsi = (spOf σ pos).at' 840 + BitVec.ofNat 64 t
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (272 - t)
  stored : Stored s.mem (σ.gpr .rdx) (Lt σ t)
  stream : SpongeStream.Stream 136 272 (spOf σ pos) σ pos s

omit hp in
theorem X_length : (X σ).length = 272 := H_length _ _

omit hp in
theorem take_succ' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

omit hp in
theorem out_byte {t : Nat} {s : State} (h : LAt σ pos t s) (ht : t < 272) : s.mem (s.gpr .rsi) = (X σ).getD t 0 := by
  have := congrArg (fun L => L.getD t 0) h.out
  rw [MlKem.bytesAt_getD _ _ ht] at this
  rw [h.rsi]; exact this

omit hp in
theorem Lt_length_le (t : Nat) : (Lt σ t).length ≤ 256 := rbFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 272) (h : LAt σ pos t s) :
    WP isa (rbBody (etaOf σ)) s fun s' => LAt σ pos (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (272 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rdx) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  have hp' := spOk (pos := pos) hp
  refine WP.mono (rbBody_ok (eta hp) s (aP := σ.gpr .rdx) h.env.rbp h.rdi (Lt_length_le t) (.of_mem hw) h.stored
    (by rw [h.rsi, at_add]; exact inScrRd hp' h.env (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have ht1 : Lt σ (t + 1) = rbStep (etaOf σ) (Lt σ t) ((X σ).getD t 0) := by
    simp only [Lt]
    rw [take_succ' _ (by rw [X_length]; omega), rbFold_snoc]
  rw [out_byte h ht, ← ht1] at hdi hst
  have hk' : Keep [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] s s' := hk.mono (by simp)
  have hsv : ∀ k, 2024 ≤ k → k + 8 ≤ 2048 →
      s'.mem.readW ((spOf σ pos).at' k) 64 = s.mem.readW ((spOf σ pos).at' k) 64 := fun k h1 h2 =>
    hf.readW (Region.contains_self _ _) (by simpa using (a_scr' hp' h2).symm) (by decide)
  refine ⟨⟨⟨hk'.2.1.trans h.env.rd, hk'.2.2.trans h.env.wr, by rw [hk'.gpr (by decide), h.env.rbx],
    by rw [hk'.gpr (by decide), h.env.rbp], by rw [hk'.gpr (by decide), h.env.r12],
    by rw [hk'.gpr (by decide), h.env.rsp],
    fun r hr => by rw [hk'.gpr (r13_not hr), h.env.cs r hr],
    (by rw [hsv 2024 (by omega) (by omega), hsv 2032 (by omega) (by omega), hsv 2040 (by omega) (by omega)];
        exact h.env.saved), h.env.frame.trans (hf.mono (by simp))⟩,
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 272) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, offAdd],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst, h.stream.frame hf
      (by simpa using (hp'.a_scr.sub_right (sub_scr0 (n := 200) (by decide))).symm)⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : J6 136 272 (spOf σ pos) σ s) (hs : SpongeStream.Stream 136 272 (spOf σ pos) σ pos s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      Env (spOf σ pos) σ s' ∧ bytesAt s'.mem ((spOf σ pos).at' 840) 272 = X σ ∧ s'.gpr .rsi = (spOf σ pos).at' 840 ∧
        s'.gpr .rdi = 0 ∧ SpongeStream.Stream 136 272 (spOf σ pos) σ pos s' := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ pos).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1, hs.mem_eq hm1⟩
  rw [hm1, h.out]; exact (H_eq _ _).symm

/-- The loop: `LAt σ pos 272` at the end. -/
theorem loop_ok {s : State} (h : J6 136 272 (spOf σ pos) σ s) (hs : SpongeStream.Stream 136 272 (spOf σ pos) σ pos s) : WP isa (rbLoopCount (etaOf σ) 272) s (LAt σ pos 272) := by
  refine WP.seq (WP.mono (lat0 h hs) fun s1 ⟨he, hout, hsi, hdi, hstream⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 272)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 272) (by decide) (by decide) (LAt σ pos) (fun t ht s hI _ =>
    WP.mono (lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _, hstream.mem_eq hm⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl


omit hp in
/-- Once the prefix has filled the polynomial, later bytes cannot change it. -/
theorem full_eq (hf : (Lt σ 272).length = 256) :
    rbFold (etaOf σ) [] (H (B σ) 544) = Lt σ 272 := by
  have he : H (B σ) 544 = X σ ++ (H (B σ) 544).drop 272 := by
    change H (B σ) 544 = H (B σ) 272 ++ _
    rw [← H_take (B σ) (d := 272) (d' := 544) (by decide), List.take_append_drop]
  rw [he, rbFold_append]
  have hl : Lt σ 272 = rbFold (etaOf σ) [] (X σ) := by
    simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]
  rw [← hl, rbFold_full hf]

/-- A successful prefix meets the original four-block postcondition. -/
theorem end_ok {s : State} (h : LAt σ pos 272 s) (hf : (Lt σ 272).length = 256) :
    WP isa (.block (retJ ++ epi)) s fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (Lt_length_le 272))
    fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun _ => ?_⟩, hg⟩
  · change (s'.gpr .rax).setWidth 32 = if (rbFold (etaOf σ) [] (H (B σ) 544)).length = 256 then 1 else 0
    rw [full_eq hf]; exact hax
  · change PolyIs s'.mem (σ.gpr .rdx) (toPoly (rbFold (etaOf σ) [] (H (B σ) 544)))
    rw [full_eq hf, hm]
    exact stored_polyIs h.stored hf

end

section
variable {σ : State} {pos : BitVec 64} (hp : rbK.pre σ)
include hp

omit hp in
/-- The prefix coefficients are the first part of the original computation. -/
theorem prefix_eq : Lt σ 272 = RejBounded.Lt σ 272 := by
  simp only [Lt, RejBounded.Lt, RejBounded.X, RejBounded.B, X, B,
    H_take (bytesAt σ.mem (σ.gpr .rdi) 66) (d := 272) (d' := 544) (by decide)]
  rw [List.take_of_length_le (by rw [H_length])]

/-- Append SHAKE output and resume from the stored coefficient count. -/
theorem continue_args_ok {s : State} (h : LAt σ pos 272 s) :
    WP isa (rbContinueArgs (etaOf σ)) s
      (RejBounded.LAt σ 272) := by
  have hp' := spOk (pos := pos) hp
  refine WP.seq (WP.mono (SpongeStream.count_ok hp' h.env) fun s1 ⟨he1, hk1, hj1, hf1⟩ => ?_)
  have hs1 := h.stream.frame hf1
    (by simpa using (disj_scr0 (P := spOf σ pos) (n := 200) (b := 2016) (m := 8) (by decide) (by decide)))
  have out1 : bytesAt s1.mem ((spOf σ pos).at' 840) 272 = X σ := by
    rw [MlKem.bytesAt_frame hf1 (by simpa using
      (disj_scr (P := spOf σ pos) (a := 840) (n := 272) (b := 2016) (m := 8) (by decide) (by decide))) (by decide)]
    exact h.out
  have stored1 := stored_frame hf1 (by simpa using (a_scr' hp' (a := 2016) (n := 8) (by decide)))
    h.stored (Lt_length_le (σ := σ) 272)
  refine WP.seq (WP.mono (SpongeStream.more_ok hp' (rate := 136) (offset := 1112) (len := 272)
    (.inl rfl) (by decide) rfl (by decide) he1 hs1) fun s2 ⟨he2, hout2, hf2⟩ => ?_)
  change bytesAt s2.mem ((spOf σ pos).at' 1112) 272 = Spec.Sha3.squeezeFrom 136
    (padded 136 Spec.Sha3.shakeSuffix (B σ)) 272 272 at hout2
  change Frame [⟨(spOf σ pos).scr, 200⟩, ⟨(spOf σ pos).at' 1112, 272⟩,
    ⟨(spOf σ pos).at' 200, 640⟩, below (σ.gpr .rsp) 16] s1.mem s2.mem at hf2
  have out2 : bytesAt s2.mem ((spOf σ pos).at' 840) 544 = RejBounded.X σ := by
    rw [show 544 = 272 + 272 from rfl, MlKem.bytesAt_add,
      show (spOf σ pos).at' 840 + BitVec.ofNat 64 272 = (spOf σ pos).at' (840 + 272) from offAdd _ _ _,
      hout2, MlKem.bytesAt_frame hf2 (SpongeStream.more_prefix_apart hp' (done := 272) (len := 272) (by decide)) (by decide), out1]
    change Spec.MlDsa.H (B σ) 272 ++ Spec.Sha3.squeezeFrom 136
      (padded 136 Spec.Sha3.shakeSuffix (B σ)) 272 272 = Spec.MlDsa.H (B σ) (272 + 272)
    rw [H_eq, H_eq, SpongeStream.squeeze_append (by decide) (by decide)]
  have hj2 : s2.mem.readW ((spOf σ pos).at' 2016) 64 = BitVec.ofNat 64 (Lt σ 272).length := by
    rw [hf2.readW (Region.contains_self _ _)
      (SpongeStream.more_word_apart hp' (done := 272) (len := 272) (k := 2016) (by decide) (by decide) (by decide)) (by decide), hj1, h.rdi]
  have stored2 := stored_frame hf2 (SpongeStream.more_poly_apart hp' (done := 272) (len := 272) (by decide)) stored1 (Lt_length_le (σ := σ) 272)
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx, .r12] (Q := fun s3 => s3.mem = s2.mem ∧
      s3.gpr .rdi = BitVec.ofNat 64 (Lt σ 272).length ∧ s3.gpr .rsi = (spOf σ pos).at' 1112 ∧
      s3.gpr .rcx = BitVec.ofNat 64 272 ∧ s3.gpr .r12 = (RejBounded.spOf σ).prm)
    (by unfold resumeArgs; simp only [List.cons_append, List.nil_append]; xrun [he2.rbx,
      (by simp only [etaOf, BitVec.ofNat_toNat, BitVec.setWidth_eq] :
        BitVec.setWidth 64 (BitVec.ofNat 32 (etaOf σ)) = (RejBounded.spOf σ).prm), (by decide : BitVec.signExtend 64 (1112 : BitVec 32) = BitVec.ofNat 64 1112), hj2, inScrRd hp' he2 (a := 2016) (n := 8) (by decide)]) (by rfl))
    fun s3 ⟨⟨hm3, hd3, hsi3, hcx3, h123⟩, hk3⟩ => ?_
  refine ⟨SpongeStream.env_param he2 hm3 (hk3.mono (by decide)) h123, by rw [hm3]; exact out2,
    ?_, by rw [hd3, prefix_eq], hcx3, ?_⟩
  · rw [hsi3]; exact (offAdd (spOf σ pos).scr 840 272).symm
  · rw [hm3, ← prefix_eq]; exact stored2

/-- Continue the same parser through the remaining two SHAKE blocks. -/
theorem continue_ok {s : State} (h : LAt σ pos 272 s) :
    WP isa (rbContinue (etaOf σ)) s fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (continue_args_ok hp h) fun s2 h2 => ?_)
  exact WP.seq (WP.mono (wp_countdown (N := 272) (by decide) (by decide)
      (fun t => RejBounded.LAt σ (272 + t))
      (fun t ht s hI _ => WP.mono (RejBounded.lat_step hp (by omega) hI) fun s' ⟨hI', hz⟩ =>
        ⟨by simpa only [Nat.add_assoc] using hI', by
          rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
          by rw [hz, hI.rcx]⟩)
      (fun _ h => h) (by simpa using h2) h2.rcx) fun _ h3 => RejBounded.end_ok hp h3)

/-- The branch after parsing: return a full polynomial, or continue its SHAKE stream. -/
theorem finish_ok {s : State} (h : LAt σ pos 272 s) :
    WP isa (.seq (.block [.alu .cmp .rdi (.imm 256)])
      (.ite .e (.block (retJ ++ epi)) (rbContinue (etaOf σ)))) s
      fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (WP.keep [.rdi] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.zf = some (s.gpr .rdi == 256)) (by xrun; change (s.gpr .rdi - 256#64 == 0#64) = (s.gpr .rdi == 256#64); rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; bv_omega) (by decide)) fun s' ⟨⟨hm, hd, hz⟩, hk⟩ => ?_)
  have h' : LAt σ pos 272 s' :=
    ⟨h.env.keep hm (hk.mono (by decide)), by rw [hm]; exact h.out,
      (hk.gpr (by decide)).trans h.rsi, hd.trans h.rdi,
      (hk.gpr (by decide)).trans h.rcx, by rw [hm]; exact h.stored, h.stream.mem_eq hm⟩
  by_cases hf : (Lt σ 272).length = 256
  · apply WP.ite true (by show s'.zf = _; rw [hz, h.rdi, hf]; rfl) (fun _ => end_ok hp h' hf)
    intro e; contradiction
  · have hz' : s'.zf = some false := by
      rw [hz, h.rdi]
      congr 1
      apply beq_eq_false_iff_ne.mpr
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Lt_length_le (σ := σ) 272; omega)] at this
      exact hf this
    apply WP.ite false hz' (fun e => by contradiction) (fun _ => continue_ok hp h')

/-- The prefix and continuation together retain the original postcondition. -/
theorem short_correct {η : Nat} (hη : etaOf σ = η) :
    WP isa (rbShort η) σ fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
  subst η
  exact WP.seq (WP.mono (pro_ok hp) fun _ h0 =>
    WP.seq (WP.mono (SpongeStream.stream_ok (initOk hp) (rate := 136) (outlen := 272) (.inl rfl) (by decide) h0)
      fun _ ⟨pos, h1, hs⟩ => WP.seq (WP.mono (loop_ok hp h1 hs) fun _ h2 => finish_ok hp h2)))

end

/-- The restored arguments and calling convention before the parameter branch. -/
structure Entry (σ s : State) : Prop where
  pre : rbK.pre s
  seed : s.gpr .rdi = σ.gpr .rdi
  eta : (s.gpr .rsi).setWidth 32 = (σ.gpr .rsi).setWidth 32
  out : s.gpr .rdx = σ.gpr .rdx
  scratch : s.gpr .rcx = σ.gpr .rcx
  bytes : bytesAt s.mem (σ.gpr .rdi) 66 = B σ
  preserved : gprPreserved σ s

section
variable {σ : State} {pos : BitVec 64} (hp : rbK.pre σ)
include hp

omit hp in
theorem Entry.post {s s' : State} (h : Entry σ s) (hp' : rbK.post s s') : rbK.post σ s' := by
  simpa only [rbK, etaOf, h.seed, h.eta, h.out, h.bytes] using hp'

omit hp in
theorem Entry.trans {s s' : State} (h : Entry σ s) (hg : gprPreserved s s') : gprPreserved σ s' := by
  refine ⟨fun r hr => (hg.1 r hr).trans (h.preserved.1 r hr), ?_⟩
  have hs : s.gpr .rsp = σ.gpr .rsp := h.preserved.1 _ (by decide)
  rw [← hs, hg.2, hs]
  exact h.preserved.2

/-- Comparing the public parameter changes only flags. -/
theorem entry_cmp_ok : WP isa (.block [.alu32 .cmp .rsi (.imm 2)]) σ fun s =>
    Entry σ s ∧ s.zf = some ((σ.gpr .rsi).setWidth 32 - 2 == 0) := by
  refine WP.mono (WP.keep [.rsi] (Q := fun s => s.mem = σ.mem ∧ s.gpr .rsi = σ.gpr .rsi ∧
      s.zf = some ((σ.gpr .rsi).setWidth 32 - 2 == 0)) (by xrun) (by decide))
    fun s ⟨⟨hm, hsi, hz⟩, hk⟩ => ?_
  have hg : ∀ r, s.gpr r = σ.gpr r := fun r => by
    by_cases hr : r = .rsi
    · subst hr; exact hsi
    · exact hk.gpr (by simp [hr])
  refine ⟨⟨?_, hg _, congrArg (BitVec.setWidth 32) (hg _), hg _, hg _, by rw [hm],
    ⟨fun r _ => hg r, by rw [hm]⟩⟩, hz⟩
  simpa only [rbK, etaOf, retR, hk.2.1, hk.2.2, hg] using hp

end

/-- The complete staged sampler has the original four-block postcondition. -/
theorem correct (σ : State) (hp : rbK.pre σ) :
    ∃ t s', Exec isa rejBoundedShort σ t s' ∧ abiPreserved σ s' ∧ rbK.post σ s' := by
  have hw : WP isa rejBoundedShort σ fun s' => rbK.post σ s' ∧ gprPreserved σ s' := by
    refine WP.seq (WP.mono (entry_cmp_ok hp) fun s ⟨h, hz⟩ => ?_)
    have hv : (σ.gpr .rsi).setWidth 32 = BitVec.ofNat 32 (etaOf σ) := by
      simp only [etaOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have he : etaOf s = etaOf σ := congrArg BitVec.toNat h.eta
    rcases eta hp with h2 | h4
    · refine WP.ite true (by show s.zf = _; rw [hz, hv, h2]; rfl)
        (fun _ => WP.mono (short_correct h.pre (he.trans h2)) fun s' ⟨hr, hg⟩ => ⟨h.post hr, h.trans hg⟩)
        (fun h => by contradiction)
    · refine WP.ite false (by show s.zf = _; rw [hz, hv, h4]; rfl)
        (fun h => by contradiction)
        (fun _ => WP.mono (short_correct h.pre (he.trans h4)) fun s' ⟨hr, hg⟩ => ⟨h.post hr, h.trans hg⟩)
  obtain ⟨t, s', he, hr, hg⟩ := hw
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he hg, hr⟩

end RejBoundedShort
end VG.Proof.MlDsa.X86_64.Sample
