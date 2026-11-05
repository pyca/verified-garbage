module
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.Sample.RejNtt
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNtt

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.SpongeStream
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

-- separate module: the prefix proofs cost more to check than their imports.

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`G(ρ, 780)` (`J6`), and the loop, iteration `t` of which starts from `LAt σ
t` with the coefficients `rnFold` samples from the first `3t` bytes of output
stored.
-/

@[expose] public section

namespace VG
materialize_code Impl.MlDsa.X86_64.Sample.rejNTTShort
end VG

namespace VG.Proof.MlDsa.X86_64.Sample

open VG VG.X86_64
open VG.Proof.MlKem.X86_64
open VG.Impl.MlDsa.X86_64.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G)
open VG.Proof.MlDsa (PolyIs)
open VG.Spec.Sha3 (bytesAt)

namespace RejNttShort

/-- The call. -/
abbrev spOf (σ : State) (pos : BitVec 64) : Sp := {RejNtt.spOf σ with prm := pos}

abbrev spInit (σ : State) : Sp := {RejNtt.spOf σ with prm := σ.gpr .r12}

/-- The seed. -/
abbrev B (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 34

/-- The XOF output. -/
abbrev X (σ : State) : List Byte := G (B σ) 780

section
variable {σ : State} {pos : BitVec 64} (hp : rnK.pre σ)
include hp

theorem spOk : SpOk (spOf σ pos) σ := SpongeStream.sp_param (RejNtt.spOk hp) pos

theorem initOk : SpOk (spInit σ) σ := SpongeStream.sp_param (RejNtt.spOk hp) (σ.gpr .r12)

omit hp in
theorem sx34 : BitVec.signExtend 64 (34 : BitVec 32) = BitVec.ofNat 64 34 := by decide

theorem pro_ok : WP isa (.block rnShortPro) σ (J0 (spInit σ) σ) := by
  have hsp := initOk hp
  refine WP.mono (WP.keep [.rbx, .rbp, .rcx, .r8] (Q := fun s =>
      s.mem = ((σ.mem.writeW ((spInit σ).at' 2024) (σ.gpr .rbx)).writeW ((spInit σ).at' 2032) (σ.gpr .rbp)).writeW
        ((spInit σ).at' 2040) (σ.gpr .r12) ∧ s.gpr .rbx = σ.gpr .rdx ∧ s.gpr .rbp = σ.gpr .rsi ∧
        s.gpr .rcx = σ.gpr .rdi ∧ s.gpr .r8 = BitVec.ofNat 64 34)
    (by unfold rnShortPro; xrun [inScrσ hsp (a := 2024) (n := 8) (by decide),
      inScrσ hsp (a := 2032) (n := 8) (by decide), inScrσ hsp (a := 2040) (n := 8) (by decide), sx34])
    (by decide)) fun s ⟨⟨hm, hb, hp, hc, h8⟩, hk⟩ =>
      pro_J0 hm hb hp (hk.gpr (by decide)) hc h8 (hk.mono (by decide))

/-! ## The loop -/

/-- The coefficients sampled after `t` iterations. -/
abbrev Lt (σ : State) (t : Nat) : List Zq := rnFold [] ((X σ).take (3 * t))

/-- At the start of iteration `t`. -/
structure LAt (σ : State) (pos : BitVec 64) (t : Nat) (s : State) : Prop where
  env : Env (spOf σ pos) σ s
  out : bytesAt s.mem ((spOf σ pos).at' 840) 780 = X σ
  rsi : s.gpr .rsi = (spOf σ pos).at' 840 + BitVec.ofNat 64 (3 * t)
  rdi : s.gpr .rdi = BitVec.ofNat 64 (Lt σ t).length
  rcx : s.gpr .rcx = BitVec.ofNat 64 (260 - t)
  stored : Stored s.mem (σ.gpr .rsi) (Lt σ t)
  stream : SpongeStream.Stream 168 780 (spOf σ pos) σ pos s

omit hp in
theorem X_length : (X σ).length = 780 := G_length _ _

omit hp in
theorem take_add_three (L : List Byte) {i : Nat} (h : i + 3 ≤ L.length) :
    L.take (i + 3) = L.take i ++ [L.getD i 0, L.getD (i + 1) 0, L.getD (i + 2) 0] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega)]
  simp only [List.take_succ_cons, List.take_zero, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show i < L.length by omega), List.getElem?_eq_getElem (show i + 1 < L.length by omega),
    List.getElem?_eq_getElem (show i + 2 < L.length by omega), Option.getD_some]

omit hp in
theorem out_byte {t : Nat} {s : State} (h : LAt σ pos t s) {k : Nat} (hk : 3 * t + k < 780) :
    s.mem (s.gpr .rsi + BitVec.ofNat 64 k) = (X σ).getD (3 * t + k) 0 := by
  have := congrArg (fun L => L.getD (3 * t + k) 0) h.out
  rw [MlKem.bytesAt_getD _ _ hk] at this
  rw [h.rsi, offAdd]; exact this

theorem lat_regions {t : Nat} {s : State} (h : LAt σ pos t s) {k : Nat} (hk : 3 * t + k < 780) :
    InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofNat 64 k) 1 := by
  rw [h.rsi, at_add, at_add]; exact inScrRd (spOk hp) h.env (by omega)

omit hp in
theorem Lt_length_le (t : Nat) : (Lt σ t).length ≤ 256 := rnFold_length_le (by simp) _

/-- An iteration, from `LAt`. -/
theorem lat_step {t : Nat} {s : State} (ht : t < 260) (h : LAt σ pos t s) :
    WP isa rnBody s fun s' => LAt σ pos (t + 1) s' ∧ s'.zf = some (BitVec.ofNat 64 (260 - t) - 1 == 0) := by
  have hw : pR (σ.gpr .rsi) ∈ s.wr := by rw [h.env.wr, hp.2.1]; simp
  refine WP.mono (rnBody_ok s (aP := σ.gpr .rsi) h.env.rbp h.rdi (Lt_length_le t) (.of_mem hw) h.stored
    (by simpa using lat_regions hp h (k := 0) (by omega)) (lat_regions hp h (by omega))
    (lat_regions hp h (by omega))) fun s' ⟨hdi, hst, hf, hsi, hcx, hz, hk⟩ => ?_
  have e0 := out_byte h (k := 0) (by omega)
  rw [add_ofNat_zero, Nat.add_zero] at e0
  have ht3 : Lt σ (t + 1) = rnStep (Lt σ t) ((X σ).getD (3 * t) 0) ((X σ).getD (3 * t + 1) 0)
      ((X σ).getD (3 * t + 2) 0) := by
    simp only [Lt]
    rw [show 3 * (t + 1) = 3 * t + 3 by omega, take_add_three _ (by rw [X_length]; omega),
      rnFold_snoc _ (by rw [List.length_take, X_length]; omega)]
  rw [e0, out_byte h (k := 1) (by omega), out_byte h (k := 2) (by omega), ← ht3] at hdi hst
  have hp' := spOk (pos := pos) hp
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
    by rw [MlKem.bytesAt_frame hf (by simpa using (a_scr' hp' (a := 840) (n := 780) (by omega)).symm)
      (by omega)]; exact h.out,
    by rw [hsi, h.rsi, offAdd, show 3 * (t + 1) = 3 * t + 3 by omega],
    hdi, by rw [hcx, h.rcx, ofNat64_pred (by omega) (by omega)]; rfl, hst, h.stream.frame hf
      (by simpa using (hp'.a_scr.sub_right (sub_scr0 (n := 200) (by decide))).symm)⟩, by rw [hz, h.rcx]⟩

omit hp in
theorem lat0 {s : State} (h : J6 168 780 (spOf σ pos) σ s) (hs : SpongeStream.Stream 168 780 (spOf σ pos) σ pos s) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)]) s fun s' =>
      Env (spOf σ pos) σ s' ∧ bytesAt s'.mem ((spOf σ pos).at' 840) 780 = X σ ∧ s'.gpr .rsi = (spOf σ pos).at' 840 ∧
        s'.gpr .rdi = 0 ∧ SpongeStream.Stream 168 780 (spOf σ pos) σ pos s' := by
  refine WP.mono (WP.keep [.rsi, .rdi] (Q := fun s' => s'.mem = s.mem ∧
      s'.gpr .rsi = (spOf σ pos).at' 840 ∧ s'.gpr .rdi = 0) (by xrun [h.env.rbx, sx840]) (by decide))
    fun s1 ⟨⟨hm1, hsi1, hdi1⟩, k1⟩ => ⟨h.env.keep hm1 (k1.mono (by decide)), ?_, hsi1, hdi1, hs.mem_eq hm1⟩
  rw [hm1, h.out]; exact (G_eq _ _).symm

/-- The loop: `LAt σ pos 260` at the end. -/
theorem loop_ok {s : State} (h : J6 168 780 (spOf σ pos) σ s) (hs : SpongeStream.Stream 168 780 (spOf σ pos) σ pos s) : WP isa (rnLoopCount 260) s (LAt σ pos 260) := by
  refine WP.seq (WP.mono (lat0 h hs) fun s1 ⟨he, hout, hsi, hdi, hstream⟩ => ?_)
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun s' => s'.mem = s1.mem ∧ s'.gpr .rcx = BitVec.ofNat 64 260)
    (by xrun) (by decide)) fun s2 ⟨⟨hm, hcx⟩, hk⟩ => ?_)
  refine wp_countdown (N := 260) (by decide) (by decide) (LAt σ pos) (fun t ht s hI _ =>
    WP.mono (lat_step hp ht hI) fun s' ⟨hI', hz⟩ => ⟨hI', ?_, by rw [hz, hI.rcx]⟩) (fun _ h => h)
    ⟨he.keep hm (hk.mono (by decide)), by rw [hm]; exact hout, by rw [hk.gpr (by decide), hsi]; simp,
      by rw [hk.gpr (by decide), hdi]; rfl, hcx, by rw [hm]; exact stored_nil _ _, hstream.mem_eq hm⟩ hcx
  rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl

omit hp in
/-- Once the prefix has filled the polynomial, later bytes cannot change it. -/
theorem full_eq (hf : (Lt σ 260).length = 256) :
    rnFold [] (G (B σ) 1008) = Lt σ 260 := by
  have he : G (B σ) 1008 = X σ ++ (G (B σ) 1008).drop 780 := by
    change G (B σ) 1008 = G (B σ) 780 ++ _
    rw [← G_take (B σ) (d := 780) (d' := 1008) (by decide), List.take_append_drop]
  rw [he, rnFold_append _ _ _ (by rw [X_length])]
  have hl : Lt σ 260 = rnFold [] (X σ) := by
    simp only [Lt]; rw [List.take_of_length_le (by rw [X_length])]
  rw [← hl, rnFold_full hf]

/-- A successful prefix meets the original six-block postcondition. -/
theorem end_ok {s : State} (h : LAt σ pos 260 s) (hf : (Lt σ 260).length = 256) :
    WP isa (.block (retJ ++ epi)) s fun s' => rnK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.mono (retEpi_ok (spOk hp) h.env h.rdi (Lt_length_le 260))
    fun s' ⟨hax, hm, hg⟩ => ⟨⟨?_, fun _ => ?_⟩, hg⟩
  · change (s'.gpr .rax).setWidth 32 = if (rnFold [] (G (B σ) 1008)).length = 256 then 1 else 0
    rw [full_eq hf]; exact hax
  · change PolyIs s'.mem (σ.gpr .rsi) (toPoly (rnFold [] (G (B σ) 1008)))
    rw [full_eq hf, hm]
    exact stored_polyIs h.stored hf

end

section
variable {σ : State} {pos : BitVec 64} (hp : rnK.pre σ)
include hp

omit hp in
/-- The prefix coefficients are the first part of the original computation. -/
theorem prefix_eq : Lt σ 260 = RejNtt.Lt σ 260 := by
  simp only [Lt, RejNtt.Lt, RejNtt.X, RejNtt.B, X, B,
    G_take (bytesAt σ.mem (σ.gpr .rdi) 34) (d := 780) (d' := 1008) (by decide)]
  rw [List.take_of_length_le (by rw [G_length])]

/-- Append SHAKE output and resume from the stored coefficient count. -/
theorem continue_args_ok {s : State} (h : LAt σ pos 260 s) :
    WP isa (rnContinueArgs) s
      (RejNtt.LAt σ 260) := by
  have hp' := spOk (pos := pos) hp
  refine WP.seq (WP.mono (SpongeStream.count_ok hp' h.env) fun s1 ⟨he1, hk1, hj1, hf1⟩ => ?_)
  have hs1 := h.stream.frame hf1
    (by simpa using (disj_scr0 (P := spOf σ pos) (n := 200) (b := 2016) (m := 8) (by decide) (by decide)))
  have out1 : bytesAt s1.mem ((spOf σ pos).at' 840) 780 = X σ := by
    rw [MlKem.bytesAt_frame hf1 (by simpa using
      (disj_scr (P := spOf σ pos) (a := 840) (n := 780) (b := 2016) (m := 8) (by decide) (by decide))) (by decide)]
    exact h.out
  have stored1 := stored_frame hf1 (by simpa using (a_scr' hp' (a := 2016) (n := 8) (by decide)))
    h.stored (Lt_length_le (σ := σ) 260)
  refine WP.seq (WP.mono (SpongeStream.more_ok hp' (rate := 168) (offset := 1620) (len := 228)
    (.inr rfl) (by decide) rfl (by decide) he1 hs1) fun s2 ⟨he2, hout2, hf2⟩ => ?_)
  change bytesAt s2.mem ((spOf σ pos).at' 1620) 228 = Spec.Sha3.squeezeFrom 168
    (padded 168 Spec.Sha3.shakeSuffix (B σ)) 780 228 at hout2
  change Frame [⟨(spOf σ pos).scr, 200⟩, ⟨(spOf σ pos).at' 1620, 228⟩,
    ⟨(spOf σ pos).at' 200, 640⟩, below (σ.gpr .rsp) 16] s1.mem s2.mem at hf2
  have out2 : bytesAt s2.mem ((spOf σ pos).at' 840) 1008 = RejNtt.X σ := by
    rw [show 1008 = 780 + 228 from rfl, MlKem.bytesAt_add,
      show (spOf σ pos).at' 840 + BitVec.ofNat 64 780 = (spOf σ pos).at' (840 + 780) from offAdd _ _ _,
      hout2, MlKem.bytesAt_frame hf2 (SpongeStream.more_prefix_apart hp' (done := 780) (len := 228) (by decide)) (by decide), out1]
    change Spec.MlDsa.G (B σ) 780 ++ Spec.Sha3.squeezeFrom 168
      (padded 168 Spec.Sha3.shakeSuffix (B σ)) 780 228 = Spec.MlDsa.G (B σ) (780 + 228)
    rw [G_eq, G_eq, SpongeStream.squeeze_append (by decide) (by decide)]
  have hj2 : s2.mem.readW ((spOf σ pos).at' 2016) 64 = BitVec.ofNat 64 (Lt σ 260).length := by
    rw [hf2.readW (Region.contains_self _ _)
      (SpongeStream.more_word_apart hp' (done := 780) (len := 228) (k := 2016) (by decide) (by decide) (by decide)) (by decide), hj1, h.rdi]
  have stored2 := stored_frame hf2 (SpongeStream.more_poly_apart hp' (done := 780) (len := 228) (by decide)) stored1 (Lt_length_le (σ := σ) 260)
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx, .r12] (Q := fun s3 => s3.mem = s2.mem ∧
      s3.gpr .rdi = BitVec.ofNat 64 (Lt σ 260).length ∧ s3.gpr .rsi = (spOf σ pos).at' 1620 ∧
      s3.gpr .rcx = BitVec.ofNat 64 76 ∧ s3.gpr .r12 = (RejNtt.spOf σ).prm)
    (by unfold resumeArgs; simp only [List.cons_append, List.nil_append]; xrun [he2.rbx,
      (by rfl : BitVec.setWidth 64 (0 : BitVec 32) = (RejNtt.spOf σ).prm), (by decide : BitVec.signExtend 64 (1620 : BitVec 32) = BitVec.ofNat 64 1620), hj2, inScrRd hp' he2 (a := 2016) (n := 8) (by decide)]) (by rfl))
    fun s3 ⟨⟨hm3, hd3, hsi3, hcx3, h123⟩, hk3⟩ => ?_
  refine ⟨SpongeStream.env_param he2 hm3 (hk3.mono (by decide)) h123, by rw [hm3]; exact out2,
    ?_, by rw [hd3, prefix_eq], hcx3, ?_⟩
  · rw [hsi3]; exact (offAdd (spOf σ pos).scr 840 780).symm
  · rw [hm3, ← prefix_eq]; exact stored2

/-- Continue the same parser through the remaining SHAKE bytes. -/
theorem continue_ok {s : State} (h : LAt σ pos 260 s) :
    WP isa (rnContinue) s fun s' => rnK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (continue_args_ok hp h) fun s2 h2 => ?_)
  exact WP.seq (WP.mono (wp_countdown (N := 76) (by decide) (by decide)
      (fun t => RejNtt.LAt σ (260 + t))
      (fun t ht s hI _ => WP.mono (RejNtt.lat_step hp (by omega) hI) fun s' ⟨hI', hz⟩ =>
        ⟨by simpa only [Nat.add_assoc] using hI', by
          rw [hI'.rcx, hI.rcx, ofNat64_pred (by omega) (by omega)]; rfl,
          by rw [hz, hI.rcx]⟩)
      (fun _ h => h) (by simpa using h2) h2.rcx) fun _ h3 => RejNtt.end_ok hp h3)

/-- The branch after parsing: return a full polynomial, or continue its SHAKE stream. -/
theorem finish_ok {s : State} (h : LAt σ pos 260 s) :
    WP isa (.seq (.block [.alu .cmp .rdi (.imm 256)])
      (.ite .e (.block (retJ ++ epi)) (rnContinue))) s
      fun s' => rnK.post σ s' ∧ gprPreserved σ s' := by
  refine WP.seq (WP.mono (WP.keep [.rdi] (Q := fun s' => s'.mem = s.mem ∧ s'.gpr .rdi = s.gpr .rdi ∧
      s'.zf = some (s.gpr .rdi == 256)) (by xrun; change (s.gpr .rdi - 256#64 == 0#64) = (s.gpr .rdi == 256#64); rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]; bv_omega) (by decide)) fun s' ⟨⟨hm, hd, hz⟩, hk⟩ => ?_)
  have h' : LAt σ pos 260 s' :=
    ⟨h.env.keep hm (hk.mono (by decide)), by rw [hm]; exact h.out,
      (hk.gpr (by decide)).trans h.rsi, hd.trans h.rdi,
      (hk.gpr (by decide)).trans h.rcx, by rw [hm]; exact h.stored, h.stream.mem_eq hm⟩
  by_cases hf : (Lt σ 260).length = 256
  · apply WP.ite true (by show s'.zf = _; rw [hz, h.rdi, hf]; rfl) (fun _ => end_ok hp h' hf)
    intro e; contradiction
  · have hz' : s'.zf = some false := by
      rw [hz, h.rdi]
      congr 1
      apply beq_eq_false_iff_ne.mpr
      intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Lt_length_le (σ := σ) 260; omega)] at this
      exact hf this
    apply WP.ite false hz' (fun e => by contradiction) (fun _ => continue_ok hp h')

end

/-- The streaming sampler retains the original six-block postcondition. -/
theorem correct (σ : State) (hp : rnK.pre σ) :
    ∃ t s', Exec isa rejNTTShort σ t s' ∧ abiPreserved σ s' ∧ rnK.post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (pro_ok hp) fun _ h0 =>
    WP.seq (WP.mono (SpongeStream.stream_ok (initOk hp) (rate := 168) (outlen := 780) (.inr rfl) (by decide) h0)
      fun _ ⟨pos, h1, hs⟩ => WP.seq (WP.mono (loop_ok hp h1 hs) fun _ h2 => finish_ok hp h2)))
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he hF.2, hF.1⟩

end RejNttShort
end VG.Proof.MlDsa.X86_64.Sample
