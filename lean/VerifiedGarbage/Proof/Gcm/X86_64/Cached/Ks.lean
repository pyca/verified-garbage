import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Aes

/-!
# The keystream of the blocks after the last group

`ksBatch_ok`: `StitchZH.ksBatch k` encrypts the `4 k` counters `c … c + 4 k - 1`
(`AInv`) in the lanes of the first `k` block registers, with the instructions
`g i` between the rounds doing what `Q` says, as `batch_ok` does, and stores
the keystream to `scratch + 768` (`ksStores_ok`) instead of adding it to the
data.
-/

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPre nb nr kp pp cb dp dR pR cR bAddr ciph sch in_sub_int)
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.Stitch (aregs)
open VG.Impl.Gcm.X86_64.StitchZH (ksStores ksBatch)
open VG.Proof.Aes.X86_64.VaesZ (ctrsZ_ok four ZFrame.of_keys zmm_lane blockAt_writeW_lane)
open VG.Proof.Aes.X86_64.AesNi (Keys aesWith_eq blockAt_frame)
open VG.Proof.Gcm.X86_64.StitchZ (AInv aregs_ok)
open VG.Spec.Gcm (Block blockAt inc32)

/-- Where the keystream goes, in the working space. -/
abbrev ksR (s₀ : State) : Region := ⟨pp s₀ + BitVec.ofNat 64 768, 256⟩

/-- The key schedule is not in the data, the working space or the counter. -/
theorem sch_frame3 {s₀ : State} (hp : SPre s₀) {m : Mem} (hf : Frame [dR s₀, pR s₀, cR s₀] s₀.mem m) :
    Spec.Aes.bytesAt m (kp s₀) (16 * (nr s₀ + 1)) = sch s₀ := by
  have hn : 16 * (nr s₀ + 1) ≤ 256 := by rcases hp.rounds with h | h | h <;> omega
  simp only [sch, Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine hf.bytes (R := ⟨kp s₀, 16 * (nr s₀ + 1)⟩) (fun r hr => ?_)
    (by show 16 * (nr s₀ + 1) ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.d_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.p_k.symm.sub_left (Region.sub_prefix hn)
  · exact hp.c_k.symm.sub_left (Region.sub_prefix hn)

/-- A 64-byte store of `b` to `r11 + d`. -/
theorem store1Z_ok (b : XReg) (d : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) 64) :
    WP isa (.block [.vmovdqu32Store (at_ .r11 d) b]) s fun s' =>
      s'.mem = s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) (s.zmm b) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.zlane r l = s.zlane r l) := by
  rw [WP.block_cons_iff]
  refine ⟨s.setMem (s.mem.writeW (s.gpr .r11 + BitVec.ofInt 64 (d : Int)) (s.zmm b)),
    by simp only [isa, exec, State.store512_eq, VG.Proof.Gcm.X86_64.Pclmul.ea_at, hin, ite_true],
    WP.block_nil ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩⟩

/-- Each register of `regs` stored to `r11 + 768 + 64 (i + k)`. -/
theorem ksStores_ok (regs : List XReg) (i : Nat) (s : State)
    (hin : ∀ k < regs.length, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((768 + 64 * (i + k) : Nat) : Int)) 64)
    (hle : 768 + 64 * (i + regs.length) ≤ 1024) :
    WP isa (.block (ksStores regs i)) s fun s' =>
      (∀ k (h : k < regs.length), ∀ l < 4,
        blockAt s'.mem (s.gpr .r11 + BitVec.ofNat 64 (768 + 16 * (4 * (i + k) + l))) =
          XBinOp.eval .pshufb (s.zlane regs[k] l) revMask) ∧
      Frame [⟨s.gpr .r11 + BitVec.ofNat 64 (768 + 64 * i), 64 * regs.length⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r l, s'.zlane r l = s.zlane r l) := by
  induction regs generalizing i s with
  | nil => exact WP.block_nil ⟨fun _ h => absurd h (by simp), Frame.refl _ _, rfl, rfl, rfl, fun _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.length_cons] at hin hle
    rw [ksStores, ← List.singleton_append, WP.block_append_iff]
    have hin0 := hin 0 (by omega)
    rw [Nat.add_zero] at hin0
    refine WP.mono (store1Z_ok b (768 + 64 * i) s hin0) fun s₁ ⟨m₁, g₁, rd₁, wr₁, z₁⟩ => ?_
    have h11 : s₁.gpr .r11 = s.gpr .r11 := by rw [g₁]
    refine WP.mono (ih (i + 1) s₁ (fun k hk => by
        rw [wr₁, h11, show i + 1 + k = i + (k + 1) by omega]; exact hin (k + 1) (by omega))
      (by omega)) fun s' ⟨hb, hf, g, rd, wr, z⟩ => ?_
    rw [h11] at hb hf
    have e₁ : BitVec.ofInt 64 ((768 + 64 * i : Nat) : Int) = BitVec.ofNat 64 (768 + 64 * i) :=
      BitVec.ofInt_natCast _ _
    rw [e₁] at m₁
    have hdj : ∀ l < 4, ∀ r ∈ [(⟨s.gpr .r11 + BitVec.ofNat 64 (768 + 64 * (i + 1)), 64 * bs.length⟩ : Region)],
        Region.Disjoint ⟨s.gpr .r11 + BitVec.ofNat 64 (768 + 16 * (4 * i + l)), 16⟩ r := by
      intro l hl
      simp only [List.mem_singleton, forall_eq]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    refine ⟨fun k hk l hl => ?_, ?_, g.trans g₁, rd.trans rd₁, wr.trans wr₁, fun r l => by rw [z, z₁]⟩
    · cases k with
      | zero =>
        simp only [List.getElem_cons_zero, Nat.add_zero]
        rw [blockAt_frame hf (hdj l hl), m₁, show 768 + 16 * (4 * i + l) = 768 + 64 * i + 16 * l by omega,
          show s.gpr .r11 + BitVec.ofNat 64 (768 + 64 * i + 16 * l) =
            s.gpr .r11 + BitVec.ofNat 64 (768 + 64 * i) + BitVec.ofNat 64 (16 * l) from (Offset.add_add _ _ _).symm,
          blockAt_writeW_lane _ _ _ hl, zmm_lane _ _ hl]
      | succ k =>
        simp only [List.getElem_cons_succ]
        have hk' : k < bs.length := by simpa using hk
        rw [show i + (k + 1) = i + 1 + k by omega, hb k hk' l hl, z₁]
    · rw [m₁] at hf
      refine (Frame.writeW (Frame.refl [⟨s.gpr .r11 + BitVec.ofNat 64 (768 + 64 * i), 64 * (bs.length + 1)⟩]
        s.mem) List.mem_cons_self _ (Offset.contains _ (Nat.le_refl _) (by omega) (by omega))).trans
        (hf.sub fun r hr => ?_)
      simp only [List.mem_singleton] at hr
      subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by omega) (by omega)⟩

theorem ctrsZ_keeps (c m i : XReg) : ∀ regs : List XReg,
    (Impl.Aes.X86_64.VaesZ.ctrsZ c m i regs).all Instr.keepsH = true
  | [] => rfl
  | _ :: bs => by
    simp only [Impl.Aes.X86_64.VaesZ.ctrsZ, List.all_append, ctrsZ_keeps c m i bs, Bool.and_true]; rfl

theorem ksStores_keeps : ∀ (regs : List XReg) (i : Nat), (ksStores regs i).all Instr.keepsH = true
  | [], _ => rfl
  | _ :: bs, i => by simp only [ksStores, List.all_cons, ksStores_keeps bs (i + 1), Bool.and_true]; rfl

theorem ksBatch_keeps (k : Nat) (g : Nat → List Instr) (hg : ∀ j, (g j).all Instr.keepsH = true) :
    (ksBatch k g).all Instr.keepsH = true := by
  simp only [ksBatch, Code.all, aes_keeps _ g hg, ctrsZ_keeps, ksStores_keeps, Bool.and_self]

/-- The `4 k` counters `c …` encrypted, with `g i` after round `i`, and their
keystream stored to `scratch + 768`. -/
theorem ksBatch_ok {s₀ : State} (hp : SPre s₀) {k : Nat} (hk : k ≤ 4) (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ aregs ∧ r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15)
    (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys (nr s₀) (sch s₀) s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ ZFrame G s s')
    (hq : ∀ j s s', Q j s → ZFrame (.xmm13 :: .xmm14 :: aregs) s s' → Q j s')
    (hqx : ∀ s s', Q 10 s → s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r l, s'.zlane r l = s.zlane r l) → Frame [ksR s₀] s.mem s'.mem → Q 10 s')
    {c : Nat} {s : State}
    (hctr : ∀ l < 4, s.zlane .xmm14 l = Nat.repeat inc32 (c + l) (cb s₀))
    (hmsk : ∀ l < 4, s.zlane .xmm0 l = revMask) (hinc : ∀ l < 4, s.zlane .xmm15 l = four)
    (hrdi : s.gpr .rdi = kp s₀) (hrsi : s.gpr .rsi = s₀.gpr .rsi) (h11 : s.gpr .r11 = pp s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hfr : Frame [dR s₀, pR s₀, cR s₀] s₀.mem s.mem)
    (hCache : VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s)
    (hgh : ∀ j, (g j).all Instr.keepsH = true) (hQ : Q 1 s) :
    WP isa (ksBatch k g) s fun s' => Q 10 s' ∧
      (∀ i < 4 * k, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [ksR s₀] s.mem s'.mem ∧ VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s' := by
  have hwp := hp.wrap_p
  have kys : ∀ t, t.gpr .rdi = kp s₀ → t.rd = s₀.rd → t.wr = s₀.wr → Frame [dR s₀, pR s₀, cR s₀] s₀.mem t.mem →
      Keys (nr s₀) (sch s₀) t := fun t h1 h2 h3 h4 =>
    ⟨by rw [h1, sch_frame3 hp h4], by rcases hp.rounds with h | h | h <;> omega,
      fun j hj => by
        rw [h2, h3, h1]
        exact Stitch.in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩
  have hK : Keys (nr s₀) (sch s₀) s := kys s hrdi hrd hwr hfr
  suffices h : WP isa (ksBatch k g) s fun s' => Q 10 s' ∧
      (∀ i < 4 * k, blockAt s'.mem (pp s₀ + BitVec.ofNat 64 (768 + 16 * i)) =
        ciph s₀ (Nat.repeat inc32 (c + i) (cb s₀))) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm13 → r ≠ .xmm14 → r ∉ aregs → r ∉ G → ∀ l < 4, s'.zlane r l = s.zlane r l) ∧
      Frame [ksR s₀] s.mem s'.mem from
    WP.mono (WP.hkeepCode (by rfl) (ksBatch_keeps k g hgh) h)
      fun t ⟨⟨hq, hks, hg', hrd', hwr', hl, hf⟩, hh⟩ => ⟨hq, hks, hg', hrd', hwr', hl, hf, hCache.keep hh
        (kys t (by rw [hg']; exact hrdi) (by rw [hrd']; exact hrd) (by rw [hwr']; exact hwr)
          (hfr.trans (hf.sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact ⟨pR s₀, by simp, Offset.sub_base _ (by omega)⟩)))⟩
  obtain ⟨hnd, h13, hx⟩ := aregs_ok
  have hnd' : (aregs.take k).Nodup := hnd.sublist (List.take_sublist _ _)
  have hx' : ∀ r ∈ aregs.take k, r ≠ .xmm14 ∧ r ≠ .xmm0 ∧ r ≠ .xmm15 := fun r hr => hx r (List.mem_of_mem_take hr)
  have h13' : .xmm13 ∉ aregs.take k := fun h => h13 (List.mem_of_mem_take h)
  have hlen : (aregs.take k).length = k := by simp [aregs]; omega
  refine WP.seq (WP.mono (WP.hkeep (ctrsZ_keeps _ _ _ _) (ctrsZ_ok .xmm14 .xmm0 .xmm15 (by decide) (by decide)
    (aregs.take k) s (cb s₀) c hnd' hx' hctr hmsk hinc)) fun s₁ ⟨⟨e₁, c₁, f₁⟩, hh₁⟩ => ?_)
  have hK₁ : Keys (nr s₀) (sch s₀) s₁ := ZFrame.of_keys hK f₁
  have hCache₁ := hCache.keep hh₁ hK₁
  have hQ₁ : Q 1 s₁ := hq _ _ _ hQ (f₁.mono fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hr)))
  refine WP.seq (WP.mono (VG.Proof.Aes.X86_64.VaesZH.aes_ok .xmm13 (aregs.take k) hnd' h13' hp.rounds g G
    (fun r h hm => (hG r h).1 (List.mem_of_mem_take hm)) Q
    (fun j hj h9 t hk hq => WP.mono (WP.hkeep (hgh j) (hg j hj h9 t hk.base hq))
      fun _ ⟨⟨hq', hf⟩, hh⟩ => ⟨hq', hf, hh⟩)
    (fun j s s' h f => hq j s s' h (f.toZFrame.mono fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_mem_take hr)))) s₁ hCache₁ hQ₁
    (by rw [f₁.gpr, hrsi]; simp)) fun s₂ ⟨e₂, hQ₂, f₂⟩ => ?_)
  -- The keystream blocks.
  have ks : ∀ j (h : j < (aregs.take k).length), ∀ l < 4,
      XBinOp.eval .pshufb (s₂.zlane (aregs.take k)[j] l) revMask =
        ciph s₀ (Nat.repeat inc32 (c + 4 * j + l) (cb s₀)) := fun j h l hl =>
    (aesWith_eq _ _ _ _ (by rw [e₂ _ (List.getElem_mem h) l hl, e₁ j h l hl])).symm
  have h11₂ : s₂.gpr .r11 = pp s₀ := by rw [f₂.gpr, f₁.gpr, h11]
  have hwr₂ : s₂.wr = s₀.wr := by rw [f₂.wr, f₁.wr, hwr]
  refine WP.mono (ksStores_ok (aregs.take k) 0 s₂ (fun j hj => by
      rw [hwr₂, h11₂]; exact in_sub_int hp.p_in (by rw [hlen] at hj; omega))
      (by rw [hlen]; omega)) fun s₃ ⟨b₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have hm₂ : s₂.mem = s.mem := by rw [f₂.mem, f₁.mem]
  rw [hm₂, h11₂] at fr₃
  rw [h11₂] at b₃
  have fr' : Frame [ksR s₀] s.mem s₃.mem := fr₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ksR s₀, List.mem_cons_self, Offset.sub _ (by omega) (by rw [hlen]; omega)⟩
  refine ⟨hqx s₂ s₃ hQ₂ g₃ rd₃ wr₃ x₃ (by rw [hm₂]; exact fr'), fun i hi => ?_,
    by rw [g₃, f₂.gpr, f₁.gpr], by rw [rd₃, f₂.rd, f₁.rd], by rw [wr₃, f₂.wr, f₁.wr],
    fun r h13' h14 hr hg' l hl => ?_, fr'⟩
  · have hj : i / 4 < (aregs.take k).length := by rw [hlen]; omega
    have := b₃ (i / 4) hj (i % 4) (by omega)
    rw [show 768 + 16 * (4 * (0 + i / 4) + i % 4) = 768 + 16 * i by omega, ks (i / 4) hj (i % 4) (by omega),
      show c + 4 * (i / 4) + i % 4 = c + i by omega] at this
    exact this
  · rw [x₃, f₂.zlane r (by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨h13', fun h => hr (List.mem_of_mem_take h), hg'⟩) l hl,
      f₁.zlane r (by
        simp only [List.mem_cons, not_or]
        exact ⟨h14, fun h => hr (List.mem_of_mem_take h)⟩) l hl]

end VG.Proof.Gcm.X86_64.StitchZH
