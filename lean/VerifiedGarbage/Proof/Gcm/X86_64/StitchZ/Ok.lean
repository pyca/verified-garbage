import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Dec
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Ctr
import VerifiedGarbage.Impl.Gcm.X86_64.StitchZ
import VerifiedGarbage.Proof.Framework.X86_64.ZLaneSse
import VerifiedGarbage.Proof.Framework.X86_64.ZFrameBlock
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Aes`. -/
section

/-!
# Interleaved counter mode and GHASH with AVX-512: a batch of sixteen blocks

`batch_ok`: `StitchZ.batch j g` encrypts the sixteen data blocks at
`rdx + 64 j` (blocks `c … c + 15`, `AInv`): the counter blocks into the four
lanes of `zmm3`–`zmm6` (`VaesZ.ctrsZ_ok`), AES of each lane
(`VaesZ.aesZ_ok`), and the XOR into the data (`VaesZ.xorDataZ_ok`). The
blocks `g i` between the rounds do what `Q` says, which neither the counter
blocks, the rounds nor the XOR (which writes only those sixteen blocks)
undo; as `Stitch.batch_ok` does with eight blocks in two lanes.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp cb dp dR pR bAddr blk ctb ciph sch sch_frame addr_eq in_sub)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (batch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok aesZ_ok xorDataZ_ok four ZFrame.of_keys)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Spec.Gcm (Block blockAt inc32 aesWith)

/-- The encryption after `c` blocks: the four counters, the mask, the
increment, the key schedule and its last round key, and the data (blocks
below `c` encrypted, the others as they were). -/
structure AInv (s₀ : State) (c : Nat) (s : State) : Prop where
  le : c ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀
  ctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀)
  msk : ∀ l < 4, s.zlane .xmm0 l = revMask
  inc : ∀ l < 4, s.zlane .xmm15 l = four
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = s₀.gpr .rsi
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  frame : Frame [VG.Proof.Gcm.X86_64.Stitch.dR s₀, pR s₀] s₀.mem s.mem
  blocks : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s.mem (bAddr s₀ k) = if k < c then ctb s₀ k else blk s₀ k
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AInv.zframe {s₀ : State} {c : Nat} {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ c s)
    (f : ZFrame rs s s') (h14 : .xmm14 ∉ rs) (h0 : .xmm0 ∉ rs) (h15 : .xmm15 ∉ rs) : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ c s' :=
  ⟨h.le, fun l hl => by rw [f.zlane _ h14 l hl]; exact h.ctr l hl,
    fun l hl => by rw [f.zlane _ h0 l hl]; exact h.msk l hl,
    fun l hl => by rw [f.zlane _ h15 l hl]; exact h.inc l hl, by rw [f.gpr]; exact h.rdi,
    by rw [f.gpr]; exact h.rsi, by rw [f.gpr]; exact h.r10, by rw [f.mem]; exact h.frame,
    fun k hk => by rw [f.mem]; exact h.blocks k hk, by rw [f.rd]; exact h.rd, by rw [f.wr]; exact h.wr⟩

theorem AInv.keys {s₀ : State} (hp : SPre s₀) {c : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ c s) :
    Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [hI.rdi, sch_frame hp hI.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [hI.rd, hI.wr, hI.rdi]
      exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem aregs_ok : aregs.Nodup ∧ .xmm13 ∉ aregs ∧ ∀ r ∈ aregs, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem batch_ok {s₀ : State} (hp : SPre s₀) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    {c j : Nat}
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, s'.zlane r l = s.zlane r l) →
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem → Q 10 s')
    (hc : c + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ c s)
    (hrdx : (s.gpr .rdx).toNat + 64 * j = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * c) (hQ : Q 1 s) :
    WP isa (batch j g) s fun s' => VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ (c + 16) s' ∧ Q 10 s' ∧ s'.gpr = s.gpr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [⟨bAddr s₀ c, 256⟩] s.mem s'.mem := by
  obtain ⟨hnd, h13, hx⟩ := VG.Proof.Gcm.X86_64.StitchZ.aregs_ok
  have hw := hp.wrap_d
  refine WP.seq (WP.mono (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide) aregs s (cb s₀) c hnd hx
    hI.ctr hI.msk hI.inc) fun s₁ ⟨e₁, c₁, f₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys (hI.keys hp) f₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => List.mem_cons_of_mem _ hr)
  refine WP.seq (WP.mono (aesZ_ok .xmm13 aregs hnd h13 hp.rounds g G (fun r h => ⟨(hG r h).1, (hG r h).2.1⟩) Q
    hg (fun j s s' h f => hq j s s' h (f.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))) s₁ hK₁ hQ₁
    (by rw [f₁.gpr, hI.rsi]; simp)
    (by rw [f₁.gpr, hI.r10, hI.rdi])) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ k (h : k < aregs.length), ∀ l < 4, XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask =
      ciph s₀ (Nat.repeat inc32 (c + 4 * k + l) (cb s₀)) := fun k h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ k h l hl])).symm
  have hrdx₂ : s₂.gpr .rdx = s.gpr .rdx := by rw [f₂.gpr, f₁.gpr]
  have addr : ∀ i, s.gpr .rdx + BitVec.ofNat 64 (64 * j + 16 * i) = bAddr s₀ (c + i) := fun i =>
    addr_eq (by omega)
  refine WP.mono (xorDataZ_ok .xmm13 .rdx aregs j s₂ hnd h13 (fun k hk => by
      rw [hrdx₂, f₂.wr, f₁.wr, hI.wr, show BitVec.ofInt 64 ((64 * (j + k) : Nat) : Int) =
        BitVec.ofNat 64 (64 * j + 16 * (4 * k)) by rw [BitVec.ofInt_natCast]; congr 1; omega, addr]
      exact in_sub hp.d_in (by simp [aregs] at hk; omega))
      (by rw [hrdx₂]; simp [aregs]; omega))
    fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, hrdx₂] at b₃ fr₃
  rw [show 64 * j = 64 * j + 16 * 0 by omega, addr, Nat.add_zero] at fr₃
  have hb3 : ∀ k (h : k < aregs.length), ∀ l < 4,
      VG.Spec.Gcm.blockAt s₃.mem (bAddr s₀ (c + (4 * k + l))) =
        VG.Spec.Gcm.blockAt s.mem (bAddr s₀ (c + (4 * k + l))) ^^^ XBinOp.eval .pshufb (s₂.zlane aregs[k] l) revMask :=
    fun k h l hl => by
      have := b₃ k h l hl
      rwa [show 16 * (4 * (j + k) + l) = 64 * j + 16 * (4 * k + l) by omega, addr] at this
  have fr' : Frame [⟨bAddr s₀ c, 256⟩] s.mem s₃.mem := by simpa [aregs] using fr₃
  have kx : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s₃.zlane r l = s.zlane r l :=
    fun r h13' h14 hr hg' l hl => by
      rw [x₃ r h13' hr l hl, f₂.zlane r (by simp [h13', hr, hg']) l hl, f₁.zlane r (by simp [h14, hr]) l hl]
  refine ⟨⟨by omega, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, by rw [g₃, f₂.gpr, f₁.gpr, hI.rdi],
    by rw [g₃, f₂.gpr, f₁.gpr, hI.rsi], by rw [g₃, f₂.gpr, f₁.gpr, hI.r10], ?_, ?_,
    by rw [rd₃, f₂.rd, f₁.rd, hI.rd], by rw [wr₃, f₂.wr, f₁.wr, hI.wr]⟩,
    hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ (fun r h1 h2 l hl => x₃ r h1 h2 l hl) (by rw [hm₂]; exact fr'),
    by rw [g₃, f₂.gpr, f₁.gpr], kx, fr'⟩
  · rw [x₃ _ (by decide) (by decide) l hl, f₂.zlane _ (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨by decide, by decide, fun h => (hG _ h).2.2.1 rfl⟩) l hl, c₁ l hl]
    simp [aregs]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.1 rfl) l hl, hI.msk l hl]
  · rw [kx _ (by decide) (by decide) (by decide) (fun h => (hG _ h).2.2.2.2 rfl) l hl, hI.inc l hl]
  · -- The data written is only in the data.
    refine hI.frame.trans (fr'.sub fun r hr => ⟨VG.Proof.Gcm.X86_64.Stitch.dR s₀, List.mem_cons_self, fun a ha => ?_⟩)
    simp only [List.mem_singleton] at hr
    subst hr
    exact VG.Proof.Aes.X86_64.AesNi.run_in hw hc (n := 16) ha
  · intro k hk
    have out : ¬ (c ≤ k ∧ k < c + 16) → VG.Spec.Gcm.blockAt s₃.mem (bAddr s₀ k) = VG.Spec.Gcm.blockAt s.mem (bAddr s₀ k) :=
      fun hn => blockAt_frame fr' fun r hr => by
        simp only [List.mem_singleton] at hr
        subst hr
        intro a h₁ h₂
        exact VG.Proof.Aes.X86_64.AesNi.run_sep hw hk hc hn h₁ h₂
    by_cases hlo : k < c
    · rw [out (by omega), hI.blocks k hk]
      simp only [hlo, show k < c + 16 by omega, ite_true]
    · by_cases hhi : k < c + 16
      · obtain ⟨i, rfl⟩ : ∃ i, k = c + (4 * (i / 4) + i % 4) := ⟨k - c, by omega⟩
        have hj : i / 4 < aregs.length := by simp [aregs]; omega
        rw [hb3 (i / 4) hj (i % 4) (by omega), hI.blocks _ hk, ks (i / 4) hj (i % 4) (by omega),
          show c + 4 * (i / 4) + i % 4 = c + (4 * (i / 4) + i % 4) by omega]
        simp only [hlo, hhi, ite_false, ite_true]
      · rw [out (by omega), hI.blocks k hk]
        simp only [hlo, hhi, ite_false]

end VG.Proof.Gcm.X86_64.StitchZ

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh`. -/
section

/-!
# Interleaved counter mode and GHASH with AVX-512: the GHASH of a group

`ghLoad_ok`: `StitchZ.ghLoad k` loads four powers from the working space
into `zmm12` and blocks `4k`–`4k + 3` into the lanes of `zmm7`, and adds
their products to each lane's (`WP.zlanes` of `Vpclmul.ldacc_ok`, the SSE
code of each lane). `fin_ok`: `StitchZ.fin` adds lanes 2 and 3 of the
products to lanes 0 and 1 (`fold_ok`), reduces both and adds them into `Y`
(`Vpclmul.reduce_lanes`, `combine_ok`). The four lanes' products, so added
and reduced, are `GHASH` over the sixteen blocks for the powers the setup
stores (`FinOk`), which needs the field: `StitchZ/Ok.lean` proves it
(`finZ`).

`GEnv`, `ghStep`, `QG` and `gq_ok` are `Stitch`'s, with four lanes, one
batch per group and the reduction after round 5.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb dp dR pR bAddr blk ctb ciph sch hk y₀ ite_t ite_f)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod)
open VG.Impl.Gcm.X86_64.Pclmul (poly at_)
open VG.Proof.Gcm.X86_64.Vpclmul (ldacc ldacc_ok reduce_lanes)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZ (ghLoad acc ord foldLanes fin gq)
open VG.Proof.Aes.X86_64.AesNi (Keys)
open VG.Proof.Gcm.X86_64.Pclmul (ea_at)
open VG.Proof.Aes.X86_64.VaesZ (load512_lane)
open VG.Spec.Gcm (Block blockAt ghashFrom)

/-! ## A load -/

/-- The lane-wise instructions of a load. -/
abbrev restZ (k : Nat) : List Instr :=
  [.zop (.zbin .vpshufb .xmm7 .xmm7 .xmm0)] ++
    (if k = 0 then [.zop (.zbin .vpxord .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 .xmm12

theorem ghLoad_eq (k : Nat) :
    ghLoad k = .vmovdqu32Load .xmm12 (at_ .r11 (64 * k)) :: .vmovdqu32Load .xmm7 (at_ .rdx (64 * k)) :: VG.Proof.Gcm.X86_64.StitchZ.restZ k := by
  simp only [ghLoad, VG.Proof.Gcm.X86_64.StitchZ.restZ, List.cons_append]

theorem lane_ld {k : Nat} (hk : k < 4) :
    zlaneSseBlock (VG.Proof.Gcm.X86_64.StitchZ.restZ k) = some (ldacc (decide (k = 0)) .xmm12) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- Lane `l` of a 64-byte load into `d`. -/
theorem zlane_load (s : State) (d : XReg) (a : Addr) {l : Nat} (hl : l < 4) :
    (s.setZ d ((s.mem.readW a 512).extractLsb' 0 128) ((s.mem.readW a 512).extractLsb' 128 128)
      ((s.mem.readW a 512).extractLsb' 256 128) ((s.mem.readW a 512).extractLsb' 384 128)).zlane d l =
      s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := by
  rw [State.zlane_setZ _ _ _ _ _ _ _ hl]
  simp only [ite_true]
  rw [pick4_lanes (fun i => (s.mem.readW a 512).extractLsb' (128 * i) 128) hl]
  exact load512_lane _ _ hl

/-- Four powers from `scratch + 64 k` into `zmm12`, and blocks `4k`–`4k + 3`
at `rdx + 64 k` added to the lanes' products with them. -/
theorem ghLoad_ok {k : Nat} (hk : k < 4) (t : State) (h0 : ∀ l < 4, t.zlane .xmm0 l = revMask)
    (hin : InRegions (t.rd ++ t.wr) (t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64)
    (hpin : InRegions (t.rd ++ t.wr) (t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64) :
    WP isa (.block (ghLoad k)) t fun t' =>
      (∀ l < 4, prod (t'.zproj l) = (prod (t.zproj l)).acc
        ((if k = 0 then t.zlane .xmm2 l else 0) ^^^
          VG.Spec.Gcm.blockAt t.mem (t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)))
        (t.mem.readW (t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l)) 128)) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] t t' := by
  let ap := t.gpr .r11 + BitVec.ofInt 64 ((64 * k : Nat) : Int)
  let ad := t.gpr .rdx + BitVec.ofInt 64 ((64 * k : Nat) : Int)
  let vp := t.mem.readW ap 512
  let t₁ := t.setZ .xmm12 (vp.extractLsb' 0 128) (vp.extractLsb' 128 128) (vp.extractLsb' 256 128)
    (vp.extractLsb' 384 128)
  let vd := t₁.mem.readW ad 512
  let t₂ := t₁.setZ .xmm7 (vd.extractLsb' 0 128) (vd.extractLsb' 128 128) (vd.extractLsb' 256 128)
    (vd.extractLsb' 384 128)
  rw [VG.Proof.Gcm.X86_64.StitchZ.ghLoad_eq, WP.block_cons_iff]
  refine ⟨t₁, by simp only [isa, exec, State.load512, ea_at, hpin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨t₂, by simp only [isa, exec, State.load512, ea_at, t₁, State.setZ_gpr, State.setZ_rd, State.setZ_wr,
    State.setZ_mem, hin, ite_true, Option.map_some]; rfl, ?_⟩
  have keep : ∀ r, r ≠ .xmm12 → r ≠ .xmm7 → ∀ l < 4, t₂.zlane r l = t.zlane r l := fun r h12 h7 l hl => by
    simp only [t₂, t₁]
    rw [State.zlane_setZ_ne _ h7 _ _ _ _ hl, State.zlane_setZ_ne _ h12 _ _ _ _ hl]
  have l12 : ∀ l < 4, t₂.zlane .xmm12 l = t.mem.readW (ap + BitVec.ofNat 64 (16 * l)) 128 := fun l hl => by
    simp only [t₂]
    rw [State.zlane_setZ_ne _ (by decide) _ _ _ _ hl]
    exact VG.Proof.Gcm.X86_64.StitchZ.zlane_load t .xmm12 ap hl
  have l7 : ∀ l < 4, t₂.zlane .xmm7 l = t.mem.readW (ad + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    VG.Proof.Gcm.X86_64.StitchZ.zlane_load t₁ .xmm7 ad hl
  refine WP.mono (WP.zlanes (VG.Proof.Gcm.X86_64.StitchZ.lane_ld hk) fun l _ => ldacc_ok _ .xmm12 (t₂.zproj l) (by decide) (by decide)
    (by decide) (by decide) (by decide))
    fun t' ⟨hk', hq⟩ => ⟨fun l hl => ?_, ?_⟩
  · rw [(hq l hl).1]
    have hp : prod (t₂.zproj l) = prod (t.zproj l) := by
      simp only [prod, State.zproj_xmm, keep .xmm8 (by decide) (by decide) l hl,
        keep .xmm9 (by decide) (by decide) l hl, keep .xmm10 (by decide) (by decide) l hl]
    simp only [hp, State.zproj_xmm, l7 l hl, l12 l hl, keep .xmm0 (by decide) (by decide) l hl, h0 l hl,
      keep .xmm2 (by decide) (by decide) l hl]
    rw [← blockAt_eq]
    by_cases h : k = 0 <;> simp only [ad, ap, h, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · refine ⟨hk'.gpr, hk'.mem, hk'.rd, hk'.wr, fun r hr l hl => ?_⟩
    have := (hq l hl).2.xmm r (fun h => hr (List.mem_cons_of_mem _ h))
    simp only [State.zproj_xmm] at this
    rw [this, keep r (fun h => hr (h ▸ List.mem_cons_self))
      (fun h => hr (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)) l hl]

/-! ## The reduction -/

/-- Lanes 2 and 3 of `r` added to lanes 0 and 1 (`VEX.256`, which clears the
upper lanes), through `zmm11`. -/
theorem fold1_ok (r : XReg) (h11 : r ≠ .xmm11) (s : State) :
    WP isa (.block [.zop (.vshufi32x4 .xmm11 r r 0x0e), .vop (.vbin .vpxor .l256 r r .xmm11)]) s fun s' =>
      (∀ l < 2, s'.lane r l = s.zlane r l ^^^ s.zlane r (l + 2)) ∧ ZFrame [.xmm11, r] s s' := by
  refine WP.zframe (by simp [vecDst, VOp.dst?, ZOp.dst]) ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  simp only [lane_vbin256, ite_true, VBinOp.sse, VG.Proof.Aes.X86_64.AesNi.eval_pxor]
  rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, zlane_vshufi32x4 _ _ _ _ _ _ (by omega),
    zlane_vshufi32x4 _ _ _ _ _ _ (by omega)]
  simp only [h11, ite_false, ite_true, shuf4Lanes]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> rfl

theorem fold_ok (s : State) :
    WP isa (.block foldLanes) s fun s' =>
      (∀ l < 2, prod (s'.proj l) = (prod (s.zproj l)).xor (prod (s.zproj (l + 2)))) ∧
      ZFrame [.xmm11, .xmm8, .xmm11, .xmm9, .xmm11, .xmm10] s s' := by
  rw [show foldLanes = [.zop (.vshufi32x4 .xmm11 .xmm8 .xmm8 0x0e), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm11)] ++
    ([.zop (.vshufi32x4 .xmm11 .xmm9 .xmm9 0x0e), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11)] ++
    [.zop (.vshufi32x4 .xmm11 .xmm10 .xmm10 0x0e), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11)]) from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fold1_ok .xmm8 (by decide) s) fun s₁ ⟨e₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fold1_ok .xmm9 (by decide) s₁) fun s₂ ⟨e₂, f₂⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fold1_ok .xmm10 (by decide) s₂) fun s' ⟨e', f'⟩ => ⟨fun l hl => ?_, f₁.comp (f₂.comp f')⟩
  have k8 : s'.lane .xmm8 l = s₁.lane .xmm8 l := by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega),
      f₂.zlane _ (by decide) l (by omega)]
  have k9 : s'.lane .xmm9 l = s₂.lane .xmm9 l := by
    rw [← State.zlane_lt2 _ _ hl, ← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega)]
  have z9 : ∀ i < 4, s₁.zlane .xmm9 i = s.zlane .xmm9 i := fun i hi => f₁.zlane _ (by decide) i hi
  have z10 : ∀ i < 4, s₂.zlane .xmm10 i = s.zlane .xmm10 i := fun i hi => by
    rw [f₂.zlane _ (by decide) i hi, f₁.zlane _ (by decide) i hi]
  simp only [prod, State.proj_xmm, State.zproj_xmm, Prod.xor, k8, k9, e₁ l hl, e₂ l hl, e' l hl,
    z9 l (by omega), z9 (l + 2) (by omega), z10 l (by omega), z10 (l + 2) (by omega)]

/-- The two lanes' blocks added into `xmm2` (`VEX.128`, so lanes 1–3 are
cleared). -/
theorem combineZ_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Vpclmul.combine) s fun s' =>
      s'.zlane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧ (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm11, .xmm2] s s' := by
  refine WP.mono (WP.zframe (is := Impl.Gcm.X86_64.Vpclmul.combine) (rs := [.xmm11, .xmm2]) (by decide)
    (Q := fun s' => s'.zlane .xmm2 0 = s.lane .xmm7 0 ^^^ s.lane .xmm7 1 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun _ ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  rw [Impl.Gcm.X86_64.Vpclmul.combine, WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨?_, fun l hl1 hl4 => ?_⟩⟩
  · simp [VBinOp.sse, VG.Proof.Gcm.X86_64.Pclmul.eval_pxor, VOp.exec, State.setV, State.zlane, State.lane]
  · simp only [VOp.exec]
    rw [State.zlane_setV128 _ _ _ _ _ hl4]
    simp [show l ≠ 0 by omega]

/-! ## The products of a group -/

/-- The input of the `k`-th load in lane `l`: block `4k + l`, with `Y` (`yl l`)
added to block 0. -/
def inp (X : Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (k l : Nat) : VG.Spec.Gcm.Block := (if k = 0 then yl l else 0) ^^^ X (4 * k + l)

/-- The products of lane `l` after the first `n` loads, in the order `ord`. -/
def accN (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (l n : Nat) : Prod :=
  (List.range n).foldl (fun p i => p.acc (VG.Proof.Gcm.X86_64.StitchZ.inp X yl (ord i) l) (P (ord i) l)) Prod.zero

theorem accN_succ (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) (l n : Nat) :
    VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l (n + 1) = (VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l n).acc (VG.Proof.Gcm.X86_64.StitchZ.inp X yl (ord n) l) (P (ord n) l) := by
  simp only [VG.Proof.Gcm.X86_64.StitchZ.accN, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- `Y` after a group: the four lanes' products, lanes 2 and 3 added to 0
and 1, reduced and added. -/
abbrev yNew (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block) : VG.Spec.Gcm.Block :=
  reduce ((VG.Proof.Gcm.X86_64.StitchZ.accN X P yl 0 4).xor (VG.Proof.Gcm.X86_64.StitchZ.accN X P yl 2 4)) ^^^ reduce ((VG.Proof.Gcm.X86_64.StitchZ.accN X P yl 1 4).xor (VG.Proof.Gcm.X86_64.StitchZ.accN X P yl 3 4))

/-- What the four lanes' products of a group add up to, for the powers `P`
(`P k l` in lane `l` of the `k`-th load): `GHASH` over its sixteen blocks, from
`Y` in lane 0 (`StitchZ/Ok.lean` proves it of the powers the setup stores). -/
def FinOk (H : VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) : Prop :=
  ∀ X yl, (∀ l, 1 ≤ l → l < 4 → yl l = 0) → VG.Proof.Gcm.X86_64.StitchZ.yNew X P yl = ghashFrom H (yl 0) ((List.range 16).map X)

/-! ## Hashing a group between the rounds -/

structure GEnv (s₀ : State) (lo : Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (s : State) :
    Prop where
  rdx : s.gpr .rdx = a
  r11 : s.gpr .r11 = pp s₀
  xs : ∀ i, lo ≤ i → i < 16 → VG.Spec.Gcm.blockAt s.mem (a + BitVec.ofNat 64 (16 * i)) = X i
  pv : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  ina : ∀ k < 4, InRegions (s.rd ++ s.wr) (a + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64
  inp : ∀ k < 4, InRegions (s.rd ++ s.wr) (pp s₀ + BitVec.ofInt 64 ((64 * k : Nat) : Int)) 64
  m0 : ∀ l < 4, s.zlane .xmm0 l = revMask

theorem GEnv.mono {s₀ : State} {lo lo' : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {s : State} (h : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s) (hl : lo ≤ lo') : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo' a X P s :=
  { h with xs := fun i hi hi' => h.xs i (Nat.le_trans hl hi) hi' }

theorem GEnv.zframe {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {s s' : State} {rs : List XReg} (h : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s) (f : ZFrame rs s s') (h0 : .xmm0 ∉ rs) :
    VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s' :=
  ⟨by rw [f.gpr]; exact h.rdx, by rw [f.gpr]; exact h.r11, fun i hi hi' => by rw [f.mem]; exact h.xs i hi hi',
    fun k hk l hl => by rw [f.mem]; exact h.pv k hk l hl, fun k hk => by rw [f.rd, f.wr]; exact h.ina k hk,
    fun k hk => by rw [f.rd, f.wr]; exact h.inp k hk, fun l hl => by rw [f.zlane _ h0 l hl]; exact h.m0 l hl⟩

theorem off4 (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (16 * (4 * k + l)) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add,
    show 64 * k + 16 * l = 16 * (4 * k + l) by omega]

theorem offp4 (a : Addr) (k l : Nat) :
    a + BitVec.ofInt 64 ((64 * k : Nat) : Int) + BitVec.ofNat 64 (16 * l) =
      a + BitVec.ofNat 64 (64 * k + 16 * l) := by
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ord_lt (n : Nat) : ord n < 4 := by
  unfold ord; split <;> decide

/-- One GHASH load, the `n`-th. -/
theorem ghStep {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} {n : Nat} (hlo : lo ≤ 4 * ord n) {s : State}
    (hE : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s) (hp : ∀ l < 4, prod (s.zproj l) = VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l n)
    (hy : ∀ l < 4, s.zlane .xmm2 l = yl l) :
    WP isa (.block (ghLoad (ord n))) s fun s' => VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s' ∧
      (∀ l < 4, prod (s'.zproj l) = VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l (n + 1)) ∧ (∀ l < 4, s'.zlane .xmm2 l = yl l) ∧
      ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s' := by
  have hk := VG.Proof.Gcm.X86_64.StitchZ.ord_lt n
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghLoad_ok hk s hE.m0 (by rw [hE.rdx]; exact hE.ina _ hk) (by rw [hE.r11]; exact hE.inp _ hk))
    fun s' ⟨p', f'⟩ => ⟨hE.zframe f' (by decide), fun l hl => ?_, fun l hl => ?_, f'⟩
  · rw [p' l hl, hp l hl, VG.Proof.Gcm.X86_64.StitchZ.accN_succ, hE.rdx, hE.r11, VG.Proof.Gcm.X86_64.StitchZ.off4, VG.Proof.Gcm.X86_64.StitchZ.offp4, hE.xs _ (by omega) (by omega),
      hE.pv _ hk l hl, hy l hl]
    rfl
  · rw [f'.zlane _ (by decide) l hl, hy l hl]

/-- The four lanes added into two, reduced, and added into `xmm2`. -/
theorem ghFin {s₀ : State} {lo : Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block} {s : State}
    (hE : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s) (h1 : ∀ l < 2, s.lane .xmm1 l = poly) :
    WP isa (.block fin) s fun s' =>
      VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ lo a X P s' ∧ s'.zlane .xmm2 0 =
        reduce ((prod (s.zproj 0)).xor (prod (s.zproj 2))) ^^^ reduce ((prod (s.zproj 1)).xor (prod (s.zproj 3))) ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0) ∧
      ZFrame [.xmm11, .xmm8, .xmm11, .xmm9, .xmm11, .xmm10, .xmm8, .xmm9, .xmm10, .xmm11, .xmm7, .xmm11, .xmm2]
        s s' := by
  rw [fin, List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.fold_ok s) fun s₁ ⟨p₁, f₁⟩ => ?_
  have h1' : ∀ l < 2, s₁.lane .xmm1 l = poly := fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, f₁.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl
  rw [WP.block_append_iff]
  refine WP.mono (WP.zframe (rs := [.xmm8, .xmm9, .xmm10, .xmm11, .xmm7]) (by decide) (reduce_lanes s₁ h1'))
    fun s₂ ⟨⟨r₂, _⟩, f₂⟩ => ?_
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.combineZ_ok s₂) fun s' ⟨c', y', f'⟩ =>
    ⟨(hE.zframe f₁ (by decide)).zframe (f₂.comp f') (by decide), ?_, y', f₁.comp (f₂.comp f')⟩
  rw [c', r₂ 0 (by decide), r₂ 1 (by decide), p₁ 0 (by decide), p₁ 1 (by decide)]

/-! ## The GHASH work of a group -/

/-- What holds before the blocks after round `j` of a group's rounds. -/
def QG (s₀ : State) (lo : Nat → Nat) (a : Addr) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block)
    (yl : Nat → VG.Spec.Gcm.Block) (j : Nat) (s : State) : Prop :=
  VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ (lo j) a X P s ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
  (if 5 < j then s.zlane .xmm2 0 = VG.Proof.Gcm.X86_64.StitchZ.yNew X P yl ∧ ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0
   else (∀ l < 4, prod (s.zproj l) = VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l (min (j - 1) 4)) ∧
     ∀ l < 4, s.zlane .xmm2 l = yl l)

/-- The registers the GHASH work writes. -/
abbrev gRegs : List XReg := [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm2]

theorem gRegs_ok : ∀ r ∈ VG.Proof.Gcm.X86_64.StitchZ.gRegs, r ≠ .xmm13 ∧ r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := by decide

theorem QG.zframe {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} {j : Nat} {s s' : State} {rs : List XReg}
    (h : VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl j s) (f : ZFrame rs s s')
    (hrs : ∀ r ∈ rs, r ∉ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg)) :
    VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl j s' := by
  obtain ⟨hE, h1, h2⟩ := h
  have k : ∀ r ∈ ([.xmm0, .xmm1, .xmm2, .xmm8, .xmm9, .xmm10] : List XReg), ∀ l < 4, s'.zlane r l = s.zlane r l :=
    fun r hr l hl => f.zlane r (fun h => hrs r h hr) l hl
  have kp : ∀ l < 4, prod (s'.zproj l) = prod (s.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, k .xmm8 (by decide) l hl, k .xmm9 (by decide) l hl,
      k .xmm10 (by decide) l hl]
  refine ⟨hE.zframe f (fun h => hrs _ h (by decide)), fun l hl => by
    rw [← State.zlane_lt2 _ _ hl, k .xmm1 (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl, ?_⟩
  split
  · rw [ite_t (by assumption)] at h2
    exact ⟨by rw [k .xmm2 (by decide) 0 (by decide)]; exact h2.1,
      fun l h1 h4 => by rw [k .xmm2 (by decide) l h4]; exact h2.2 l h1 h4⟩
  · rw [ite_f (by assumption)] at h2
    exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl, fun l hl => by rw [k .xmm2 (by decide) l hl]; exact h2.2 l hl⟩

/-- `batch_ok`'s obligation for the GHASH work between the rounds. -/
theorem gq_ok {s₀ : State} {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block}
    {yl : Nat → VG.Spec.Gcm.Block} (hmono : ∀ j, lo j ≤ lo (j + 1))
    (hrd : ∀ j, 1 ≤ j → j ≤ 4 → lo j ≤ 4 * ord (j - 1)) :
    ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl j s →
      WP isa (.block (gq j)) s fun s' => VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl (j + 1) s' ∧ ZFrame VG.Proof.Gcm.X86_64.StitchZ.gRegs s s' := by
  intro j hj1 hj9 s _ ⟨hE, h1, h2⟩
  by_cases hl4 : j ≤ 4
  · -- A load.
    have hlo := hrd j hj1 hl4
    rw [ite_f (by omega)] at h2
    simp only [gq, show 1 ≤ j ∧ j ≤ 4 from ⟨hj1, hl4⟩, and_self, ite_true]
    rw [show min (j - 1) 4 = j - 1 by omega] at h2
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghStep hlo hE h2.1 h2.2) fun s' ⟨hE', p', y', f'⟩ =>
      ⟨⟨hE'.mono (hmono j), fun l hl => by
        rw [← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl,
        ?_⟩, f'.mono (by decide)⟩
    rw [ite_f (by omega), show min (j + 1 - 1) 4 = j - 1 + 1 by omega]
    exact ⟨p', y'⟩
  · by_cases h5 : j = 5
    · -- The reduction.
      subst h5
      rw [ite_f (by omega)] at h2
      simp only [gq, show ¬ (1 ≤ 5 ∧ 5 ≤ 4) by omega, ite_false, ite_true]
      refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghFin hE h1) fun s' ⟨hE', y0, y1, f'⟩ =>
        ⟨⟨hE'.mono (hmono 5), fun l hl => by
          rw [← State.zlane_lt2 _ _ hl, f'.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact h1 l hl,
          ?_⟩, f'.mono (by decide)⟩
      rw [ite_t (by omega)]
      refine ⟨by rw [y0, h2.1 0 (by decide), h2.1 1 (by decide), h2.1 2 (by decide), h2.1 3 (by decide)]; rfl, y1⟩
    · -- Nothing.
      have hg : gq j = [] := by
        simp only [gq, show ¬ (1 ≤ j ∧ j ≤ 4) by omega, ite_false, h5]
      rw [hg]
      refine WP.block_nil ⟨⟨hE.mono (hmono j), h1, ?_⟩, ZFrame.refl _ _⟩
      rw [ite_t (by omega)]
      rw [ite_t (by omega)] at h2
      exact h2

end VG.Proof.Gcm.X86_64.StitchZ

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop`. -/
section

/-!
# Interleaved counter mode and GHASH with AVX-512: the loops

`EInv s₀ P e s`: `e` groups of sixteen blocks are encrypted (`AInv`), the
first `e - 1` hashed into `Y` (lane 0 of `zmm2`, the other lanes 0), the
powers `P` in the working space; `rdx` points to group `e - 1`, the next to
hash. `body_ok`: a body encrypts group `e` (`batch_ok`) while it hashes group
`e - 1` between its rounds (`gq_ok`), which it does not write (`QG.data`).
`DInv` and `dbody_ok` are the same for decryption, which hashes each group
during its own rounds, before its blocks are overwritten. The setup is
`Stitch`'s, and then the four lanes (`setupZ_ok`); the stores at the end are
`Stitch`'s. `encTail_ok` and `decTail_ok` are the loops after the setup, for
any powers whose products add up to `GHASH` (`FinOk`), without the field:
`StitchZ/Ok.lean` proves `StitchOk` of `StitchZ.enc` and `StitchZ.dec`
(`stitch_ok`) from them.
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk nb nr kp pp cp yp cb dp dR pR cR yR bAddr blk ctb ciph
  sch hk y₀ ite_t ite_f addr_eq in_sub in_sub_int in_rdwr ghash_append16 ghash16 blockAt_writeW_sep' blocks_ctr32)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce prod toNat_ofNat_lt ofNat_sub_ofNat)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (aregs storeCtr storeY)
open VG.Impl.Gcm.X86_64.StitchZ (batch body gq ghLoad ord setupZ first lastG dbody fin)
open VG.Proof.Aes.X86_64.AesNi (blockAt_frame run_sep Keys)
open VG.Proof.Aes.X86_64.VaesZ (four)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom inc32)

/-! ## Helpers -/

/-- `Prod.zero` in the products of the four lanes (`VEX.256` clears the
upper lanes). -/
theorem zeroZ_ok (s : State) :
    WP isa (.block Impl.Gcm.X86_64.Vpclmul.zero) s fun s' =>
      (∀ l < 4, prod (s'.zproj l) = Prod.zero) ∧ ZFrame [.xmm8, .xmm9, .xmm10] s s' := by
  refine WP.mono (WP.zframe (is := Impl.Gcm.X86_64.Vpclmul.zero) (rs := [.xmm8, .xmm9, .xmm10]) (by decide)
    (Q := fun s' => ∀ l < 4, prod (s'.zproj l) = Prod.zero) ?_) fun _ h => h
  have z : ∀ (t : State) (r : XReg) (l : Nat), l < 4 →
      ((VOp.vbin .vpxor .l256 r r r).exec t).zlane r l = 0 := fun t r l hl => by
    simp only [VOp.exec, State.zlane, State.lane, State.setV, ite_true, VBinOp.sse,
      VG.Proof.Aes.X86_64.AesNi.eval_pxor, BitVec.xor_self]
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> simp
  rw [Impl.Gcm.X86_64.Vpclmul.zero, WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil fun l hl => ?_⟩
  have n : ∀ (t : State) (r d : XReg), r ≠ d → ∀ l,
      ((VOp.vbin .vpxor .l256 d d d).exec t).zlane r l = t.zlane r l :=
    fun t r d h l => by simp only [VOp.exec]; exact State.zlane_setV_ne _ _ h _ _ _
  simp (disch := decide) only [prod, State.zproj_xmm, Prod.zero, n, z _ _ _ hl]

/-- `vpshufb x, x', ymm0` (`VEX.128`) and a 16-byte store of `x` to `[b]`. -/
theorem store16Z_ok (x x' : XReg) (b : Reg) (s : State) (h0 : s.lane .xmm0 0 = revMask)
    (hin : InRegions s.wr (s.gpr b) 16) :
    WP isa (.block [.vop (.vbin .vpshufb .l128 x x' .xmm0), .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ b 0) x])
      s fun s' => s'.mem = s.mem.writeW (s.gpr b) (XBinOp.eval .pshufb (s.lane x' 0) revMask) ∧ s'.gpr = s.gpr ∧
        s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ x → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have hin' : InRegions s.wr (s.gpr b + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 := by
    rw [BitVec.ofInt_natCast, BitVec.add_zero]; exact hin
  simp only [State.lane] at h0
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.setV, State.store128_eq,
    VG.Proof.Gcm.X86_64.Pclmul.ea_at, VBinOp.sse, State.lane, ite_true, hin', h0, Option.some.injEq,
    exists_eq_left']
  refine ⟨by rw [BitVec.ofInt_natCast, BitVec.add_zero]; simp, rfl, rfl, rfl, fun r hr l hl => ?_⟩
  simp [State.zlane, State.lane, hr]

/-! ## The GHASH state, kept by the data written -/

theorem QG.data {s₀ : State} (hp : SPre s₀) {lo : Nat → Nat} {a : Addr} {X : Nat → VG.Spec.Gcm.Block}
    {P : Nat → Nat → VG.Spec.Gcm.Block} {yl : Nat → VG.Spec.Gcm.Block} {j c g : Nat}
    (hc : c + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (hg : 16 * g + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) (ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * g)
    (hsep : ∀ i, lo j ≤ i → i < 16 → ¬ (c ≤ 16 * g + i ∧ 16 * g + i < c + 16))
    {t t' : State} (h : VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl j t) (hgpr : t'.gpr = t.gpr) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hlane : ∀ r, r ≠ .xmm13 → r ∉ aregs → ∀ l < 4, t'.zlane r l = t.zlane r l)
    (hf : Frame [⟨bAddr s₀ c, 256⟩] t.mem t'.mem) : VG.Proof.Gcm.X86_64.StitchZ.QG s₀ lo a X P yl j t' := by
  have hw := hp.wrap_d
  obtain ⟨hE, h1, h2⟩ := h
  have kp : ∀ l < 4, prod (t'.zproj l) = prod (t.zproj l) := fun l hl => by
    simp only [prod, State.zproj_xmm, hlane .xmm8 (by decide) (by decide) l hl,
      hlane .xmm9 (by decide) (by decide) l hl, hlane .xmm10 (by decide) (by decide) l hl]
  refine ⟨⟨by rw [hgpr]; exact hE.rdx, by rw [hgpr]; exact hE.r11, fun i hi hi' => ?_, fun k hk l hl => ?_,
    fun k hk => by rw [hrd, hwr]; exact hE.ina k hk, fun k hk => by rw [hrd, hwr]; exact hE.inp k hk,
    fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact hE.m0 l hl⟩,
    fun l hl => by
      rw [← State.zlane_lt2 _ _ hl, hlane _ (by decide) (by decide) l (by omega), State.zlane_lt2 _ _ hl]
      exact h1 l hl, ?_⟩
  · have e : a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * g + i) := addr_eq (by omega)
    rw [e, blockAt_frame hf fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      intro x h₁ h₂
      exact run_sep hw (by omega) hc (hsep i hi hi') h₁ h₂]
    have := hE.xs i hi hi'
    rwa [e] at this
  · rw [hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)]
    exact hE.pv k hk l hl
  · split
    · rw [ite_t (by assumption)] at h2
      exact ⟨by rw [hlane _ (by decide) (by decide) 0 (by decide)]; exact h2.1,
        fun l h1 h4 => by rw [hlane _ (by decide) (by decide) l h4]; exact h2.2 l h1 h4⟩
    · rw [ite_f (by assumption)] at h2
      exact ⟨fun l hl => by rw [kp l hl]; exact h2.1 l hl,
        fun l hl => by rw [hlane _ (by decide) (by decide) l hl]; exact h2.2 l hl⟩

/-! ## The encryption loop -/

structure EInv (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ (16 * e) s
  one : 1 ≤ e
  rdx : (s.gpr .rdx).toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1))
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * (e - 1))).map (ctb s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The end of an encryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 32`. -/
theorem nextE_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 32)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 32)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16, e32,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The end of a decryption body: `add rdx, 256`, `sub r9, 16`, `cmp r9, 16`. -/
theorem nextD_ok (s : State) :
    WP isa (.block [.alu .add .rdx (.imm 256), .alu .sub .r9 (.imm 16), .alu .cmp .r9 (.imm 16)]) s
      fun s' => s'.gpr .rdx = s.gpr .rdx + 256 ∧ s'.gpr .r9 = s.gpr .r9 - 16 ∧
        s'.cf = some (decide ((s.gpr .r9 - 16).toNat < 16)) ∧
        (∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r) ∧ (∀ r l, s'.zlane r l = s.zlane r l) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e256, e16,
    Option.bind_some, Option.some.injEq, exists_eq_left', and_self]
  exact ⟨trivial, trivial, rfl, fun r h1 h2 => by simp only [h2, ↓reduceIte, h1], fun _ _ => rfl, trivial⟩

/-- The powers in the working space are kept by the data written. -/
theorem keepP {s₀ : State} (hp : SPre s₀) {c : Nat} (hc : c + 16 ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {m m' : Mem}
    (hf : Frame [⟨bAddr s₀ c, 256⟩] m m') {k l : Nat} (hk : k < 4) (hl : l < 4) :
    m'.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = m.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  exact hf.readW (r := pR s₀) (Offset.contains_base _ (by omega) (by omega)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.d_p.symm.sub_right (Offset.sub_base _ (by omega))) (by decide)

theorem body_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s) :
    WP isa body s fun s' => VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32)) := by
  have hw := hp.wrap_d
  have h1e := hI.one
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.zeroZ_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hE₁ : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  have hrdx₁ : (s₁.gpr .rdx).toNat + 64 * 4 = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 16 * (16 * e) := by
    rw [f₁.gpr]; show a.toNat + _ = _; omega
  -- The group, with the loads of the previous group after rounds 1–4 and the reduction after round 5.
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.batch_ok hp gq VG.Proof.Gcm.X86_64.StitchZ.gRegs VG.Proof.Gcm.X86_64.StitchZ.gRegs_ok (VG.Proof.Gcm.X86_64.StitchZ.QG s₀ (fun _ => 0) a X P yl)
    (VG.Proof.Gcm.X86_64.StitchZ.gq_ok (fun _ => Nat.le_refl _) (fun _ _ _ => Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha (fun i _ hi => by omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 4) (by omega) hA₁ hrdx₁
    ⟨hE₁, fun l hl => by
      rw [← State.zlane_lt2 _ _ hl, f₁.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.nextE_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1 - 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1; omega
  refine ⟨⟨hA', by omega, ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, VG.Proof.Gcm.X86_64.StitchZ.keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [← State.zlane_lt2 _ _ hl, fl, State.zlane_lt2 _ _ hl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, BitVec.toNat_add, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by show a.toNat + 256 < 2 ^ 64; omega)]
    show a.toNat + 256 = _
    rw [ha, show e + 1 - 1 = (e - 1) + 1 by omega, Nat.mul_succ, Nat.add_assoc]
  · rw [fl, h2.1, hf X yl hI.y1,
      show e + 1 - 1 = (e - 1) + 1 by omega, ghash_append16, ← hI.y]
  · rw [fcf, hr9, toNat_ofNat_lt (by omega), show e + 1 - 1 = e by omega]

/-! ## The setup -/

theorem State.zlane_setV256 (s : State) (d r : XReg) (lo hi : BitVec 128) (l : Nat) :
    (s.setV .l256 d lo hi).zlane r l =
      if r = d then (if l = 0 then lo else if l = 1 then hi else 0) else s.zlane r l := by
  simp only [State.zlane, State.lane, State.setV]
  by_cases h : r = d
  · subst h
    rcases (by omega : l = 0 ∨ l = 1 ∨ 2 ≤ l) with rfl | rfl | hl
    · simp
    · simp
    · simp [show ¬ l < 2 by omega, show l ≠ 0 by omega, show l ≠ 1 by omega]
  · simp [h]

theorem paddd_two_two : XBinOp.eval .paddd VG.Proof.Aes.X86_64.Vaes.two VG.Proof.Aes.X86_64.Vaes.two = four := by
  decide

theorem lane0_zlane (t : State) (r : XReg) : t.lane r 0 = t.zlane r 0 := rfl
theorem lane1_zlane (t : State) (r : XReg) : t.lane r 1 = t.zlane r 1 := rfl

theorem shuf44_0 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 0 = a 0 := rfl
theorem shuf44_1 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 1 = a 1 := rfl
theorem shuf44_2 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 2 = b 0 := rfl
theorem shuf44_3 (a b : Nat → BitVec 128) : shuf4Lanes a b 0x44 3 = b 1 := rfl

structure Ready (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ 0 s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.zlane .xmm2 0 = y₀ s₀
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- The four lanes, from the two of `Stitch.setup`: the powers of the `k`-th
load are the `2k`-th and `2k + 1`-th of `Stitch`'s. -/
theorem setupZ_ok {s₀ : State} {P : Nat → Nat → VG.Spec.Gcm.Block} {s : State} (hR : Stitch.Ready s₀ P s) :
    WP isa (.block setupZ) s (VG.Proof.Gcm.X86_64.StitchZ.Ready s₀ fun k l => P (2 * k + l / 2) (l % 2)) := by
  refine WP.mono (WP.zframe (is := setupZ) (rs := [.xmm13, .xmm14, .xmm15, .xmm15, .xmm0, .xmm2]) (by decide)
    (Q := fun s' => (∀ l < 4, s'.zlane .xmm14 l = Nat.repeat inc32 l (cb s₀)) ∧ (∀ l < 4, s'.zlane .xmm0 l = revMask) ∧
      (∀ l < 4, s'.zlane .xmm15 l = four) ∧ s'.zlane .xmm2 0 = s.lane .xmm2 0 ∧
      (∀ l, 1 ≤ l → l < 4 → s'.zlane .xmm2 l = 0)) ?_) fun s' ⟨⟨c14, m0, i15, y0, y1⟩, f⟩ => ?_
  · have c0 : s.xmm .xmm14 = Nat.repeat inc32 0 (cb s₀) := by
      have h := hR.a.ctr 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have c1 : s.ymmHi .xmm14 = Nat.repeat inc32 1 (cb s₀) := by
      have h := hR.a.ctr 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have i0 : s.xmm .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.a.inc 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have i1 : s.ymmHi .xmm15 = VG.Proof.Aes.X86_64.Vaes.two := by
      have h := hR.a.inc 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    have m0 : s.xmm .xmm0 = revMask := by
      have h := hR.a.msk 0 (by decide); simp only [State.lane, ite_true] at h; exact h
    have m1 : s.ymmHi .xmm0 = revMask := by
      have h := hR.a.msk 1 (by decide); simp only [State.lane, Nat.one_ne_zero, ite_false] at h; exact h
    rw [setupZ]
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, ?_⟩
    rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, ?_,
      fun l hl1 hl4 => ?_⟩⟩
    all_goals simp only [VOp.exec]
    all_goals try rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
    all_goals try omega
    all_goals simp (disch := decide) only [VG.Proof.Gcm.X86_64.StitchZ.lane0_zlane, VG.Proof.Gcm.X86_64.StitchZ.lane1_zlane, State.zlane_setV_ne, zlane_vshufi32x4, State.zlane_setV256,
      State.zlane_setV128, VG.Proof.Gcm.X86_64.StitchZ.shuf44_0, VG.Proof.Gcm.X86_64.StitchZ.shuf44_1, VG.Proof.Gcm.X86_64.StitchZ.shuf44_2, VG.Proof.Gcm.X86_64.StitchZ.shuf44_3, reduceCtorEq,
      ↓reduceIte, VBinOp.sse, Nat.one_ne_zero]
    all_goals simp only [State.zlane, State.lane, ite_true, ite_false, Nat.one_ne_zero,
      show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide]
    all_goals first
      | exact c0 | exact c1 | exact m0 | exact m1
      | (rw [c0, i0, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [c1, i1, VG.Proof.Aes.X86_64.Vaes.paddd_two]; rfl)
      | (rw [i0]; exact VG.Proof.Gcm.X86_64.StitchZ.paddd_two_two) | (rw [i1]; exact VG.Proof.Gcm.X86_64.StitchZ.paddd_two_two)
  · have hA := hR.a
    refine ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.zero_add], m0, i15, by rw [f.gpr]; exact hA.rdi,
      by rw [f.gpr]; exact hA.rsi, by rw [f.gpr]; exact hA.r10, by rw [f.mem]; exact hA.frame,
      fun k hk => by rw [f.mem]; exact hA.blocks k hk, by rw [f.rd]; exact hA.rd, by rw [f.wr]; exact hA.wr⟩,
      by rw [f.gpr]; exact hR.rdx, by rw [f.gpr]; exact hR.rax, fun r h1 h2 h3 => by rw [f.gpr]; exact hR.gpr r h1 h2 h3,
      fun k hk l hl => ?_, fun l hl => ?_, by rw [y0]; exact hR.y, y1⟩
    · rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega]
      exact hR.pw _ (by omega) _ (by omega)
    · rw [← State.zlane_lt2 _ _ hl, f.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact hR.m1 l hl

/-- The first group, with nothing between its rounds. -/
theorem first_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} {s : State} (hR : VG.Proof.Gcm.X86_64.StitchZ.Ready s₀ P s) :
    WP isa first s (VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P 1) := by
  have hwp := hp.wrap_p
  have hwd := hp.wrap_d
  have h16 := hp.nb16
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have none : ∀ j, 1 ≤ j → j ≤ 9 → ∀ t, Keys (nr s₀) (sch s₀) t → (fun _ _ => True) j t →
      WP isa (.block ((fun _ => []) j)) t fun t' => (fun (_ : Nat) (_ : State) => True) (j + 1) t' ∧ ZFrame [] t t' :=
    fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, ZFrame.refl _ _⟩
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.batch_ok hp (fun _ => []) [] (by simp) (fun _ _ => True) none
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ => trivial) (c := 0) (j := 0) (by omega) hR.a
    (by rw [hR.rdx]) trivial) fun s₁ ⟨hA₁, _, hg₁, hl₁, hm₁⟩ => ?_
  have lk : ∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → ∀ l < 4, s₁.zlane r l = s.zlane r l :=
    fun r h13 h14 hr l hl => hl₁ r h13 h14 hr (by simp) l hl
  refine ⟨by simpa using hA₁, Nat.le_refl _, by rw [hg₁, hR.rdx]; simp, ?_, by rw [hg₁]; exact hR.rax,
    fun r h1 h2 _ h4 => by rw [hg₁]; exact hR.gpr r h1 h2 h4,
    fun k hk l hl => by rw [VG.Proof.Gcm.X86_64.StitchZ.keepP hp (by omega) hm₁ hk hl]; exact hR.pw k hk l hl,
    fun l hl => by
      rw [← State.zlane_lt2 _ _ hl, lk _ (by decide) (by decide) (by decide) l (by omega), State.zlane_lt2 _ _ hl]
      exact hR.m1 l hl,
    by rw [lk _ (by decide) (by decide) (by decide) 0 (by decide), hR.y]; simp [ghashFrom],
    fun l h1 h4 => by rw [lk _ (by decide) (by decide) (by decide) l h4]; exact hR.y1 l h1 h4⟩
  rw [hg₁, hR.gpr _ (by decide) (by decide) (by decide)]; simp

/-- `cmp r9, 32`. -/
theorem cmpE_ok {s₀ : State} {P : Nat → Nat → VG.Spec.Gcm.Block} {e : Nat} {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s) :
    WP isa (.block [.alu .cmp .r9 (.imm 32)]) s fun s' =>
      VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32)) := by
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  have e32 : BitVec.signExtend 64 (32 : BitVec 32) = 32 := by decide
  have hr9 := hI.r9
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    hr9, e32, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨{ hI with a := { hI.a with } }, ?_⟩
  rw [toNat_ofNat_lt (by omega)]; rfl

theorem loopE_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {s : State}
    (hI : VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P 1 s) (hcf : s.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32))) :
    WP isa (.ite .b (.block []) (.loop body .ae)) s fun s' => ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s' := by
  have hm := hp.nbm
  have fin : ∀ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e - 1) < 32 → ∀ t, VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e t → ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e t :=
    fun e he t hI => ⟨e, by have := hI.a.le; have := hI.one; omega, hI⟩
  refine WP.ite (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (1 - 1) < 32)) (by simp only [eval, hcf]) (fun h => ?_) (fun h => ?_)
  · exact WP.block_nil (fin 1 (by simpa using h) s hI)
  · let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s
    have hstep : ∀ m s, I m s → WP isa body s (fun s' =>
        (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s') ∨
        (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
      rintro m s ⟨e, rfl, he, hI⟩
      refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.body_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e < 32
      · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
          fin (e + 1) (by simpa using hlt) s' hI'⟩
      · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
          VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by have := hI.one; omega, e + 1, rfl, by omega, hI'⟩
    exact WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * 1) s ⟨1, rfl, by simp at h; omega, hI⟩

/-! ## The last group, and the stores -/

/-- The loads `0 … n − 1` of a group. -/
theorem ghRun_ok {s₀ : State} {a : Addr} {X : Nat → VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block} {yl : Nat → VG.Spec.Gcm.Block} :
    ∀ n, n ≤ 4 → ∀ s, VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ 0 a X P s → (∀ l < 4, prod (s.zproj l) = Prod.zero) →
      (∀ l < 4, s.zlane .xmm2 l = yl l) →
      WP isa (.block ((List.range n).flatMap fun i => ghLoad (ord i))) s fun s' => VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ 0 a X P s' ∧
        (∀ l < 4, prod (s'.zproj l) = VG.Proof.Gcm.X86_64.StitchZ.accN X P yl l n) ∧ (∀ l < 4, s'.zlane .xmm2 l = yl l) ∧
        ZFrame [.xmm12, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11] s s'
  | 0, _, s, hE, hz, hy => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨hE, fun l hl => by rw [hz l hl]; rfl, hy, ZFrame.refl _ _⟩
  | n + 1, hn, s, hE, hz, hy => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghRun_ok n (by omega) s hE hz hy) fun s₁ ⟨hE₁, p₁, y₁, f₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghStep (Nat.zero_le _) hE₁ p₁ y₁) fun s' ⟨hE', p', y', f'⟩ => ⟨hE', p', y', f₁.trans f'⟩

theorem final_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {e : Nat}
    (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.EInv s₀ P e s) :
    WP isa (.block (storeCtr ++ lastG ++ storeY)) s (EPost s₀) := by
  have hw := hp.wrap_d
  have hwp := hp.wrap_p
  have h1e := hI.one
  have hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have cP : ∀ k < 4, ∀ l < 4, Region.Disjoint ⟨pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l), 16⟩ (cR s₀) :=
    fun k hk l hl => hp.p_c.sub_left (Offset.sub_base _ (by omega))
  rw [hI.rax] at m₁
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => ctb s₀ (16 * (e - 1) + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * (e - 1) := hI.rdx
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  simp only [lastG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.zeroZ_ok s₁) fun s₂ ⟨z₂, f₂⟩ => ?_
  have hE₂ : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ 0 a X P s₂ :=
    { rdx := by rw [f₂.gpr, g₁]
      r11 := by rw [f₂.gpr, g₁, hr11]
      xs := fun i _ hi => by
        rw [f₂.mem, m₁, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * (e - 1) + i) from addr_eq (by omega),
          blockAt_writeW_sep' (cD _ (by omega)) rfl, hI.a.blocks _ (by omega)]
        simp only [show 16 * (e - 1) + i < 16 * e by omega, ite_true]
        rfl
      pv := fun k hk l hl => by
        rw [f₂.mem, m₁, Mem.readW_writeW_sep ((cP k hk l hl).sep (Region.contains_self _ _) (Region.contains_self _ _))
          (by decide)]
        exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * (e - 1) + 64 * k) from
            addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₂.rd, f₂.wr, rd₁, wr₁, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ _ (by decide) l hl]; exact hI.a.msk l hl }
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghRun_ok (yl := yl) 4 (Nat.le_refl _) s₂ hE₂ z₂
    (fun l hl => by rw [f₂.zlane _ (by decide) l hl, l₁ _ (by decide) l hl])) fun s₃ ⟨hE₃, p₃, _, f₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.ghFin hE₃ (fun l hl => by
      rw [← State.zlane_lt2 _ _ hl, f₃.zlane _ (by decide) l (by omega), f₂.zlane _ (by decide) l (by omega),
        l₁ _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact hI.m1 l hl))
    fun s₄ ⟨_, y4, _, f₄⟩ => ?_
  rw [p₃ 0 (by decide), p₃ 1 (by decide), p₃ 2 (by decide), p₃ 3 (by decide)] at y4
  have hm0₄ : s₄.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), f₄.zlane _ (by decide) 0 (by decide), f₃.zlane _ (by decide) 0 (by decide),
      f₂.zlane _ (by decide) 0 (by decide), l₁ _ (by decide) 0 (by decide)]; exact hI.a.msk 0 (by decide)
  have g₄ : s₄.gpr = s.gpr := by rw [f₄.gpr, f₃.gpr, f₂.gpr, g₁]
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₄ hm0₄ (by
      rw [g₄, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr, hI.gpr _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.y_in)) fun s₅ ⟨m₅, g₅, rd₅, wr₅, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [g₄, hrcx] at m₅
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem, f₃.mem, f₂.mem]
  rw [m₄, m₁] at m₅
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₅.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₅, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  have hdata := blocks_ctr32 hb
  refine ⟨hdata, ?_, ?_, ?_, ?_, by
      show s₅.rd = _; rw [rd₅, f₄.rd, f₃.rd, f₂.rd, rd₁, hI.a.rd], by
      show s₅.wr = _; rw [wr₅, f₄.wr, f₃.wr, f₂.wr, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₅.mem (cp s₀) = _
    rw [m₅, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show VG.Spec.Gcm.blockAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀))
    rw [show VG.Spec.Gcm.blocksAt s₅.mem (VG.Proof.Gcm.X86_64.Stitch.dp s₀) (VG.Proof.Gcm.X86_64.Stitch.nb s₀) = (List.range (16 * e)).map (ctb s₀) from by
        rw [← he]; simp only [VG.Spec.Gcm.blocksAt]
        exact List.map_congr_left fun k hk => hb k (by simpa using hk),
      m₅, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide), y4]
    refine (hf X yl hI.y1).trans ?_
    rw [show 16 * e = 16 * ((e - 1) + 1) by congr 1; omega, ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · show Frame _ s₀.mem s₅.mem
    rw [m₅]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₅.gpr r = _
    rw [g₅, g₄]; exact hI.gpr r h1 h2 h3 h4

/-- The encryption after the setup. -/
theorem encTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {s : State}
    (hR : VG.Proof.Gcm.X86_64.StitchZ.Ready s₀ P s) :
    WP isa (.seq first (.seq (.block [.alu .cmp .r9 (.imm 32)])
      (.seq (.ite .b (.block []) (.loop body .ae)) (.block (storeCtr ++ lastG ++ storeY))))) s (EPost s₀) := by
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.first_ok hp hR) fun s₂ hI₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.cmpE_ok hI₂) fun s₃ ⟨hI₃, hcf⟩ => ?_)
  exact WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.loopE_ok hp hf hI₃ hcf) fun s₄ ⟨e, he, hI₄⟩ => VG.Proof.Gcm.X86_64.StitchZ.final_ok hp hf he hI₄)

/-! ## Decryption -/

structure DInv (s₀ : State) (P : Nat → Nat → VG.Spec.Gcm.Block) (e : Nat) (s : State) : Prop where
  a : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ (16 * e) s
  rdx : s.gpr .rdx = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * e)
  r9 : s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e)
  rax : s.gpr .rax = cp s₀
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  pw : ∀ k < 4, ∀ l < 4, s.mem.readW (pp s₀ + BitVec.ofNat 64 (64 * k + 16 * l)) 128 = P k l
  m1 : ∀ l < 2, s.lane .xmm1 l = poly
  y : s.zlane .xmm2 0 = ghashFrom (hk s₀) (y₀ s₀) ((List.range (16 * e)).map (blk s₀))
  y1 : ∀ l, 1 ≤ l → l < 4 → s.zlane .xmm2 l = 0

/-- Which blocks of the group the GHASH loads to come still read: all until
they are done, after round 4. -/
abbrev loD (j : Nat) : Nat := if j < 5 then 0 else 16

theorem dbody_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {e : Nat}
    (he : 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀) {s : State} (hI : VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P e s) :
    WP isa dbody s fun s' => VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P (e + 1) s' ∧ s'.cf = some (decide (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16)) := by
  have hw := hp.wrap_d
  have hn : VG.Proof.Gcm.X86_64.Stitch.nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  let a := s.gpr .rdx
  let X : Nat → VG.Spec.Gcm.Block := fun i => blk s₀ (16 * e + i)
  let yl : Nat → VG.Spec.Gcm.Block := fun l => s.zlane .xmm2 l
  have ha : a.toNat = (VG.Proof.Gcm.X86_64.Stitch.dp s₀).toNat + 256 * e := by
    show (s.gpr .rdx).toNat = _
    rw [hI.rdx, BitVec.toNat_add, toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hr11 : s.gpr .r11 = pp s₀ := hI.gpr .r11 (by decide) (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.zeroZ_ok s) fun s₁ ⟨z₁, f₁⟩ => ?_)
  have hE₁ : VG.Proof.Gcm.X86_64.StitchZ.GEnv s₀ 0 a X P s₁ :=
    { rdx := by rw [f₁.gpr]
      r11 := by rw [f₁.gpr, hr11]
      xs := fun i _ hi => by
        rw [f₁.mem, show a + BitVec.ofNat 64 (16 * i) = bAddr s₀ (16 * e + i) from addr_eq (by omega),
          hI.a.blocks _ (by omega)]
        simp only [show ¬ 16 * e + i < 16 * e by omega, ite_false]
        rfl
      pv := fun k hk l hl => by rw [f₁.mem]; exact hI.pw k hk l hl
      ina := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr, BitVec.ofInt_natCast,
          show a + BitVec.ofNat 64 (64 * k) = VG.Proof.Gcm.X86_64.Stitch.dp s₀ + BitVec.ofNat 64 (256 * e + 64 * k) from addr_eq (by omega)]
        exact in_rdwr (in_sub hp.d_in (by omega))
      inp := fun k hk => by
        rw [f₁.rd, f₁.wr, hI.a.rd, hI.a.wr]
        exact in_rdwr (in_sub_int hp.p_in (by omega))
      m0 := fun l hl => by rw [f₁.zlane _ (by decide) l hl]; exact hI.a.msk l hl }
  have hA₁ := hI.a.zframe f₁ (by decide) (by decide) (by decide)
  -- The group is hashed after rounds 1–4, before its blocks are decrypted, and reduced after round 5.
  refine WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.batch_ok hp gq VG.Proof.Gcm.X86_64.StitchZ.gRegs VG.Proof.Gcm.X86_64.StitchZ.gRegs_ok (VG.Proof.Gcm.X86_64.StitchZ.QG s₀ VG.Proof.Gcm.X86_64.StitchZ.loD a X P yl)
    (VG.Proof.Gcm.X86_64.StitchZ.gq_ok (fun j => by simp only [VG.Proof.Gcm.X86_64.StitchZ.loD]; split <;> split <;> omega) (fun j hj1 hj4 => by
      simp only [VG.Proof.Gcm.X86_64.StitchZ.loD, show j < 5 by omega, ite_true]; exact Nat.zero_le _))
    (fun j t t' h f => h.zframe f (by decide))
    (fun t t' h hg hrd hwr hl hf => QG.data hp (by omega) (by omega) ha
      (fun i hi _ => by have : 16 ≤ i := hi; omega) h hg hrd hwr hl hf)
    (c := 16 * e) (j := 0) (by omega) hA₁ (by rw [f₁.gpr]; show a.toNat + _ = _; omega)
    ⟨hE₁, fun l hl => by
      rw [← State.zlane_lt2 _ _ hl, f₁.zlane _ (by decide) l (by omega), State.zlane_lt2 _ _ hl]; exact hI.m1 l hl,
      by rw [ite_f (by decide)]
         exact ⟨fun l hl => z₁ l hl, fun l hl => by rw [f₁.zlane _ (by decide) l hl]⟩⟩)
    fun s₂ ⟨hA₂, hQ₂, hg₂, hl₂, hm₂⟩ => ?_)
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.nextD_ok s₂) fun s' ⟨frdx, fr9, fcf, fg, fl, fm, frd, fwr⟩ => ?_
  obtain ⟨_, h1', h2⟩ := hQ₂
  rw [ite_t (by decide)] at h2
  have gk : ∀ r, r ≠ .rdx → r ≠ .r9 → s'.gpr r = s.gpr r := fun r h1 h2 => by rw [fg r h1 h2, hg₂, f₁.gpr]
  have hA' : VG.Proof.Gcm.X86_64.StitchZ.AInv s₀ (16 * (e + 1)) s' := by
    rw [show 16 * (e + 1) = 16 * e + 16 by omega]
    exact ⟨hA₂.le, fun l hl => by rw [fl]; exact hA₂.ctr l hl, fun l hl => by rw [fl]; exact hA₂.msk l hl,
      fun l hl => by rw [fl]; exact hA₂.inc l hl,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.rdi, by rw [fg _ (by decide) (by decide)]; exact hA₂.rsi,
      by rw [fg _ (by decide) (by decide)]; exact hA₂.r10, by rw [fm]; exact hA₂.frame,
      fun k hk => by rw [fm]; exact hA₂.blocks k hk, by rw [frd]; exact hA₂.rd, by rw [fwr]; exact hA₂.wr⟩
  have hr9 : s₂.gpr .r9 - 16 = BitVec.ofNat 64 (VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1)) := by
    rw [hg₂, f₁.gpr, hI.r9, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl,
      ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  refine ⟨⟨hA', ?_, by rw [fr9, hr9], by rw [gk _ (by decide) (by decide)]; exact hI.rax,
    fun r h1 h2 h3 h4 => by rw [gk r h2 h3]; exact hI.gpr r h1 h2 h3 h4,
    fun k hk l hl => by rw [fm, VG.Proof.Gcm.X86_64.StitchZ.keepP hp (by omega) hm₂ hk hl, f₁.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [← State.zlane_lt2 _ _ hl, fl, State.zlane_lt2 _ _ hl]; exact h1' l hl, ?_,
    fun l h1 h4 => by rw [fl]; exact h2.2 l h1 h4⟩, ?_⟩
  · rw [frdx, hg₂, f₁.gpr, hI.rdx, BitVec.add_assoc, show (256 : BitVec 64) = BitVec.ofNat 64 256 from rfl,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [fl, h2.1]
    refine (hf X yl hI.y1).trans ?_
    rw [ghash_append16]
    exact congrArg (fun y => ghashFrom (hk s₀) y ((List.range 16).map X)) hI.y
  · rw [fcf, hr9, toNat_ofNat_lt (by omega)]

theorem dfinal_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} {e : Nat} (he : VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e) {s : State}
    (hI : VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P e s) :
    WP isa (.block (storeCtr ++ storeY)) s (DPost s₀) := by
  have hw := hp.wrap_d
  have hm0 : s.lane .xmm0 0 = revMask := by rw [← State.zlane_lt2 _ _ (by decide)]; exact hI.a.msk 0 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.store16Z_ok .xmm13 .xmm14 .rax s hm0 (by rw [hI.rax, hI.a.wr]; exact hp.c_in))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁, l₁⟩ => ?_
  rw [hI.rax] at m₁
  have hrcx : s.gpr .rcx = VG.Proof.Gcm.X86_64.Stitch.yp s₀ := hI.gpr _ (by decide) (by decide) (by decide) (by decide)
  rw [show storeY = [.vop (.vbin .vpshufb .l128 .xmm2 .xmm2 .xmm0),
    .vmovdquStore .l128 (VG.Impl.Gcm.X86_64.Pclmul.at_ .rcx 0) .xmm2] ++ [.vop .vzeroupper] from rfl,
    WP.block_append_iff]
  have hm0₁ : s₁.lane .xmm0 0 = revMask := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide), State.zlane_lt2 _ _ (by decide)]; exact hm0
  refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.store16Z_ok .xmm2 .xmm2 .rcx s₁ hm0₁
      (by rw [g₁, wr₁, hI.a.wr, hrcx]; exact hp.y_in)) fun s₂ ⟨m₂, g₂, rd₂, wr₂, _⟩ => ?_
  rw [WP.block_cons_iff]; refine ⟨_, rfl, WP.block_nil ?_⟩
  have e2 : s₁.lane .xmm2 0 = s.zlane .xmm2 0 := by
    rw [← State.zlane_lt2 _ _ (by decide), l₁ _ (by decide) 0 (by decide)]
  rw [g₁, hrcx, m₁, e2] at m₂
  have cD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (cR s₀) := fun k hk =>
    hp.d_c.sub_left (Offset.sub_base _ (by omega))
  have yD : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, Region.Disjoint ⟨bAddr s₀ k, 16⟩ (VG.Proof.Gcm.X86_64.Stitch.yR s₀) := fun k hk =>
    hp.d_y.sub_left (Offset.sub_base _ (by omega))
  have hb : ∀ k < VG.Proof.Gcm.X86_64.Stitch.nb s₀, VG.Spec.Gcm.blockAt s₂.mem (bAddr s₀ k) = ctb s₀ k := fun k hk => by
    rw [m₂, blockAt_writeW_sep' (yD k hk) rfl, blockAt_writeW_sep' (cD k hk) rfl, hI.a.blocks k hk]
    simp only [show k < 16 * e by omega, ite_true]
  refine ⟨blocks_ctr32 hb, ?_, ?_, ?_, ?_, by show s₂.rd = _; rw [rd₂, rd₁, hI.a.rd],
    by show s₂.wr = _; rw [wr₂, wr₁, hI.a.wr]⟩
  · show VG.Spec.Gcm.blockAt s₂.mem (cp s₀) = _
    rw [m₂, blockAt_writeW_sep' hp.c_y rfl, VG.Proof.Gcm.X86_64.blockAt_store, ← State.zlane_lt2 _ _ (by decide),
      hI.a.ctr 0 (by decide), Nat.add_zero, he]
  · show VG.Spec.Gcm.blockAt s₂.mem (VG.Proof.Gcm.X86_64.Stitch.yp s₀) = _
    rw [m₂, VG.Proof.Gcm.X86_64.blockAt_store, hI.y, he]
    rfl
  · show Frame _ s₀.mem s₂.mem
    rw [m₂]
    exact ((hI.a.frame.mono fun r hr => by simp at hr ⊢; rcases hr with h | h <;> simp [h]).writeW
      (r := cR s₀) (by simp) _ (Region.contains_self _ _)).writeW (r := VG.Proof.Gcm.X86_64.Stitch.yR s₀) (by simp) _
      (Region.contains_self _ _)
  · intro r h1 h2 h3 h4
    show s₂.gpr r = _
    rw [g₂, g₁]; exact hI.gpr r h1 h2 h3 h4

/-- The decryption after the setup. -/
theorem decTail_ok {s₀ : State} (hp : SPre s₀) {P : Nat → Nat → VG.Spec.Gcm.Block} (hf : VG.Proof.Gcm.X86_64.StitchZ.FinOk (hk s₀) P) {s₁ : State}
    (hR : VG.Proof.Gcm.X86_64.StitchZ.Ready s₀ P s₁) : WP isa (.seq (.loop dbody .ae) (.block (storeCtr ++ storeY))) s₁ (DPost s₀) := by
  have hm := hp.nbm
  have h16 := hp.nb16
  have hI₁ : VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P 0 s₁ :=
    ⟨hR.a, by rw [hR.rdx]; simp, by rw [hR.gpr _ (by decide) (by decide) (by decide)]; simp, hR.rax,
      fun r h1 h2 _ h4 => hR.gpr r h1 h2 h4, hR.pw, hR.m1, by rw [hR.y]; simp [ghashFrom], hR.y1⟩
  let I : Nat → State → Prop := fun m s => ∃ e, m = VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * e ∧ 16 * (e + 1) ≤ VG.Proof.Gcm.X86_64.Stitch.nb s₀ ∧ VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P e s
  have hstep : ∀ m s, I m s → WP isa dbody s (fun s' =>
      (eval .ae s' = some false ∧ ∃ e, VG.Proof.Gcm.X86_64.Stitch.nb s₀ = 16 * e ∧ VG.Proof.Gcm.X86_64.StitchZ.DInv s₀ P e s') ∨
      (eval .ae s' = some true ∧ ∃ m' < m, I m' s')) := by
    rintro m s ⟨e, rfl, he, hI⟩
    refine WP.mono (VG.Proof.Gcm.X86_64.StitchZ.dbody_ok hp hf he hI) fun s' ⟨hI', hcf'⟩ => ?_
    by_cases hlt : VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1) < 16
    · exact .inl ⟨by simp only [eval, hcf', hlt, decide_true, Option.map_some, Bool.not_true],
        e + 1, by omega, hI'⟩
    · exact .inr ⟨by simp only [eval, hcf', hlt, decide_false, Option.map_some, Bool.not_false],
        VG.Proof.Gcm.X86_64.Stitch.nb s₀ - 16 * (e + 1), by omega, e + 1, rfl, by omega, hI'⟩
  exact WP.seq (WP.mono (WP.loop (M := isa) I hstep (VG.Proof.Gcm.X86_64.Stitch.nb s₀) s₁ ⟨0, by simp, by omega, hI₁⟩)
    fun s₂ ⟨e, he, hI₂⟩ => VG.Proof.Gcm.X86_64.StitchZ.dfinal_ok hp he hI₂)

end VG.Proof.Gcm.X86_64.StitchZ

end

/- Proofs formerly in `VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok`. -/
section

/-!
# Interleaved counter mode and GHASH with AVX-512: the field

The only module of `Proof/Gcm/X86_64/StitchZ/` that computes in the field
(`Proof/Gcm/Poly.lean`), so that few modules import its algebra:

* `setup_ok`: the setup is `Stitch`'s (`Stitch.setup_ok`, which computes the
  powers in the field), and then the four lanes (`setupZ_ok`): the powers of
  the `k`-th load in lane `l` are `x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ`.
* `finZ`: with those powers, the four lanes' products of a group, added and
  reduced, are `GHASH` over its sixteen blocks (`FinOk`).
* `stitch_ok`: both loops meet their contracts (`StitchOk`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPre EPost DPost StitchOk hk zero_xor_b ghash16)
open VG.Proof.Gcm.X86_64.Pclmul (Prod reduce φ_reduce)
open VG.Impl.Gcm.X86_64.StitchZ (ord setup enc dec)
open VG.Spec.Gcm (Block mul)

/-! ## The products of a group, in the field -/

theorem val_xor (p q : Prod) : (p.xor q).val = p.val + q.val := by
  simp only [Prod.val, Prod.xor, φ_xor]; ring

/-- Sixteen blocks, in `Q`, the products in the lanes and order of a group. -/
theorem step16Z (H Y X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ X₈ X₉ X₁₀ X₁₁ X₁₂ X₁₃ X₁₄ X₁₅ T₁ T₂ T₃ T₄ T₅ T₆ T₇ T₈ T₉ T₁₀ T₁₁ T₁₂ T₁₃ T₁₄ T₁₅ T₁₆ : VG.Spec.Gcm.Block)
    (h₁ : x * φ T₁ = φ H) (h₂ : x * φ T₂ = φ H ^ 2) (h₃ : x * φ T₃ = φ H ^ 3) (h₄ : x * φ T₄ = φ H ^ 4) (h₅ : x * φ T₅ = φ H ^ 5) (h₆ : x * φ T₆ = φ H ^ 6) (h₇ : x * φ T₇ = φ H ^ 7) (h₈ : x * φ T₈ = φ H ^ 8) (h₉ : x * φ T₉ = φ H ^ 9) (h₁₀ : x * φ T₁₀ = φ H ^ 10) (h₁₁ : x * φ T₁₁ = φ H ^ 11) (h₁₂ : x * φ T₁₂ = φ H ^ 12) (h₁₃ : x * φ T₁₃ = φ H ^ 13) (h₁₄ : x * φ T₁₄ = φ H ^ 14) (h₁₅ : x * φ T₁₅ = φ H ^ 15) (h₁₆ : x * φ T₁₆ = φ H ^ 16) :
    reduce (((((Prod.zero.acc X₄ T₁₂).acc X₈ T₈).acc X₁₂ T₄).acc (Y ^^^ X₀) T₁₆).xor
        ((((Prod.zero.acc X₆ T₁₀).acc X₁₀ T₆).acc X₁₄ T₂).acc X₂ T₁₄)) ^^^
      reduce (((((Prod.zero.acc X₅ T₁₁).acc X₉ T₇).acc X₁₃ T₃).acc X₁ T₁₅).xor
        ((((Prod.zero.acc X₇ T₉).acc X₁₁ T₅).acc X₁₅ T₁).acc X₃ T₁₃)) =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((Y ^^^ X₀)) H ^^^ X₁) H ^^^ X₂) H ^^^ X₃) H ^^^ X₄) H ^^^ X₅) H ^^^ X₆) H ^^^ X₇) H ^^^ X₈) H ^^^ X₉) H ^^^ X₁₀) H ^^^ X₁₁) H ^^^ X₁₂) H ^^^ X₁₃) H ^^^ X₁₄) H ^^^ X₁₅) H := by
  apply φ_inj
  simp only [φ_xor, φ_reduce, VG.Proof.Gcm.X86_64.StitchZ.val_xor, Prod.val_acc, Prod.val_zero, φ_mul]
  linear_combination (φ Y + φ X₀) * h₁₆ + φ X₁ * h₁₅ + φ X₂ * h₁₄ + φ X₃ * h₁₃ + φ X₄ * h₁₂ + φ X₅ * h₁₁ + φ X₆ * h₁₀ + φ X₇ * h₉ + φ X₈ * h₈ + φ X₉ * h₇ + φ X₁₀ * h₆ + φ X₁₁ * h₅ + φ X₁₂ * h₄ + φ X₁₃ * h₃ + φ X₁₄ * h₂ + φ X₁₅ * h₁

/-- The four lanes' products of a group, added and reduced: `GHASH` over the
sixteen blocks. -/
theorem finZ_mul (H : VG.Spec.Gcm.Block) (X : Nat → VG.Spec.Gcm.Block) (P : Nat → Nat → VG.Spec.Gcm.Block) (yl : Nat → VG.Spec.Gcm.Block)
    (hy : ∀ l, 1 ≤ l → l < 4 → yl l = 0)
    (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    VG.Proof.Gcm.X86_64.StitchZ.yNew X P yl =
      mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul (mul ((yl 0 ^^^ X 0)) H ^^^ X 1) H ^^^ X 2) H ^^^ X 3) H ^^^ X 4) H ^^^ X 5) H ^^^ X 6) H ^^^ X 7) H ^^^ X 8) H ^^^ X 9) H ^^^ X 10) H ^^^ X 11) H ^^^ X 12) H ^^^ X 13) H ^^^ X 14) H ^^^ X 15) H := by
  have h₁ := hP 3 (by decide) 3 (by decide)
  rw [show 16 - 4 * 3 - 3 = 1 from rfl, pow_one] at h₁
  have h₂ := hP 3 (by decide) 2 (by decide)
  have h₃ := hP 3 (by decide) 1 (by decide)
  have h₄ := hP 3 (by decide) 0 (by decide)
  have h₅ := hP 2 (by decide) 3 (by decide)
  have h₆ := hP 2 (by decide) 2 (by decide)
  have h₇ := hP 2 (by decide) 1 (by decide)
  have h₈ := hP 2 (by decide) 0 (by decide)
  have h₉ := hP 1 (by decide) 3 (by decide)
  have h₁₀ := hP 1 (by decide) 2 (by decide)
  have h₁₁ := hP 1 (by decide) 1 (by decide)
  have h₁₂ := hP 1 (by decide) 0 (by decide)
  have h₁₃ := hP 0 (by decide) 3 (by decide)
  have h₁₄ := hP 0 (by decide) 2 (by decide)
  have h₁₅ := hP 0 (by decide) 1 (by decide)
  have h₁₆ := hP 0 (by decide) 0 (by decide)
  simp only [Nat.reduceMul, Nat.reduceSub] at h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆
  simp only [VG.Proof.Gcm.X86_64.StitchZ.yNew, VG.Proof.Gcm.X86_64.StitchZ.accN, List.range_succ, List.range_zero, List.nil_append, List.foldl_append, List.foldl_cons,
    List.foldl_nil, ord, VG.Proof.Gcm.X86_64.StitchZ.inp, hy 1 (by decide) (by decide), hy 2 (by decide) (by decide),
    hy 3 (by decide) (by decide), ↓reduceIte, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
    Nat.zero_add, Nat.add_zero, zero_xor_b]
  exact VG.Proof.Gcm.X86_64.StitchZ.step16Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄ h₁₅ h₁₆

/-- The products of a group, for powers `x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ`. -/
theorem finZ {H : VG.Spec.Gcm.Block} {P : Nat → Nat → VG.Spec.Gcm.Block} (hP : ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l)) :
    VG.Proof.Gcm.X86_64.StitchZ.FinOk H P := fun X yl hy => by
  rw [ghash16]; exact VG.Proof.Gcm.X86_64.StitchZ.finZ_mul H X P yl hy hP

/-! ## Both loops -/

theorem setup_ok {s₀ : State} (hp : SPre s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, VG.Proof.Gcm.X86_64.StitchZ.Ready s₀ P s ∧
      ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ (hk s₀) ^ (16 - 4 * k - l) := by
  rw [setup, WP.block_append_iff]
  exact WP.mono (Stitch.setup_ok hp) fun _ ⟨_, hR, hpw⟩ => WP.mono (VG.Proof.Gcm.X86_64.StitchZ.setupZ_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact hpw _ (by omega) _ (by omega)⟩

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPre s₀) : WP isa enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.setup_ok hp) fun _ ⟨_, hR, hpw⟩ => VG.Proof.Gcm.X86_64.StitchZ.encTail_ok hp (VG.Proof.Gcm.X86_64.StitchZ.finZ hpw) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPre s₀) : WP isa dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (VG.Proof.Gcm.X86_64.StitchZ.setup_ok hp) fun _ ⟨_, hR, hpw⟩ => VG.Proof.Gcm.X86_64.StitchZ.decTail_ok hp (VG.Proof.Gcm.X86_64.StitchZ.finZ hpw) hR)

/-- Both loops meet their contracts. -/
theorem stitch_ok : StitchOk Impl.Gcm.X86_64.StitchZ.enc Impl.Gcm.X86_64.StitchZ.dec :=
  ⟨fun _ hp => VG.Proof.Gcm.X86_64.StitchZ.enc_ok hp, fun _ hp => VG.Proof.Gcm.X86_64.StitchZ.dec_ok hp⟩

end VG.Proof.Gcm.X86_64.StitchZ

end
