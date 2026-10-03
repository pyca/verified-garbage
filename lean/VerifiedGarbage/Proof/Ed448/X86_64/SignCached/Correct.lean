import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Calls
import VerifiedGarbage.Proof.Ed448.X86_64.SignCached.Pre
import VerifiedGarbage.Proof.Ed448.Signing

/-!
# Ed448 signing with a cached public key on x86-64: correctness

The frame's body leaves `R ‖ S` in `out`, `Spec.Ed448.sign` of the private
key, the context and the message, given the public key of the private key
(`body_ok`): each piece is kept by the code that runs after it, which writes
elsewhere. The frame's push gives `Ctx` (`entry_ctx`). From a state
satisfying `signCachedContract X86_64.abi 464`, `signCached` meets the
contract and the ABI (`signCached_wp`), for any proof of
`vg_ed448_scalar_base` (`BaseOk`).
-/

namespace VG.Proof.Ed448.X86_64.SignCached

open VG VG.X86_64 VG.Impl.Ed448.X86_64.SignCached
open VG.Impl.Ed448.X86_64.Verify (stk)
open VG.Proof.Ed448.X86_64.Verify (add_add ea_stk x0 bytesAt_length bytesAt_congr)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.Sha3 (bytesAt)

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- Bytes apart from every region of a frame are kept. -/
theorem keepB {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

/-- Two pieces of the frame. -/
theorem ff (L : Lay) {d n e k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 448) (he : e + k ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.SP + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

/-- A piece of the frame and the 16 bytes below it. -/
theorem fb (L : Lay) {d n : Nat} (hd : d + n ≤ 448) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.B, 16⟩ := by
  rw [spd]; exact Offset.disjoint_base _ (by omega) (by omega)

/-- A piece of the frame and one of `out`. -/
theorem fo (hL : L.Ok) {d n e k : Nat} (hd : d + n ≤ 448) (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ ⟨L.out + BitVec.ofNat 64 e, k⟩ := by
  rw [spd]; exact (hL.stk_r hL.kOut (d := 16 + d) (n := n) (by omega)).sub_right (Offset.sub_base _ he)

/-- A piece of `out` and `scratch`; and the 16 bytes below the frame. -/
theorem ox (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR :=
  (hL.o_r hL.xOut.symm he)

theorem ob (hL : L.Ok) {e k : Nat} (he : e + k ≤ 114) :
    Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ :=
  (k_r hL (hL.kOut.sub_right (Offset.sub_base _ he))).symm

theorem out0 (L : Lay) : L.out + BitVec.ofNat 64 0 = L.out := x0 _

/-- The header and the prefix after a hash into the frame. -/
theorem bytes_drop (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  have a := Proof.X25519.bytesAt_add m p 57 57
  have l := Proof.X25519.length_bytesAt m p 57
  change (Spec.X25519.bytesAt m p (57 + 57)).drop 57 = Spec.X25519.bytesAt m (p + BitVec.ofNat 64 57) 57
  rw [a, List.drop_left' l]

theorem bytes_split (m : Mem) (p : Addr) :
    bytesAt m p 114 = bytesAt m p 57 ++ bytesAt m (p + BitVec.ofNat 64 57) 57 :=
  Proof.X25519.bytesAt_add m p 57 57

/-- The first ten bytes of `dom4(0, C)`, then `C`, are `dom4(0, C)`. -/
theorem hash_eq (L : Lay) (c X Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (hdrBytes L ++ c ++ X ++ Y) 114 = Spec.Ed448.hash c (X ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, hdrBytes, hc, List.append_assoc]

theorem hash_eq' (L : Lay) (c X P Y : List Byte) (hc : c.length = L.ctxLen.toNat) :
    Spec.Sha3.shake256 (hdrBytes L ++ c ++ X ++ P ++ Y) 114 = Spec.Ed448.hash c (X ++ P ++ Y) := by
  simp only [Spec.Ed448.hash, Spec.Ed448.dom4, hdrBytes, hc, List.append_assoc]

theorem body_ok (hb : BaseOk) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t)
    (hpk : Spec.Ed448.bytesAt m₀ L.pk 57 = Spec.Ed448.publicKey (Spec.Ed448.bytesAt m₀ L.seed 57)) :
    WP isa body t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 114 = Spec.Ed448.sign (bytesAt m₀ L.seed 57)
        (bytesAt m₀ L.ctx L.ctxLen.toNat) (bytesAt m₀ L.msg L.len.toNat) := by
  refine WP.seq (WP.mono (hdr_ok hL hc) fun t1 ⟨hc1, hh⟩ => ?_)
  refine WP.seq (WP.mono (seedHash_ok hL hc1) fun t2 ⟨hc2, f2, hS⟩ => ?_)
  refine WP.seq (WP.mono (prune_ok hL hc2) fun t3 ⟨hc3, f3, hs⟩ => ?_)
  refine WP.seq (WP.mono (nonceHash_ok hL hc3) fun t4 ⟨hc4, f4, hN⟩ => ?_)
  refine WP.seq (WP.mono (red_ok hL hc4 (d := 384) (by omega) (by omega) (by omega)) fun t5 ⟨hc5, f5, hR⟩ => ?_)
  refine WP.seq (WP.mono (base_ok hb hL hc5) fun t6 ⟨hc6, f6, hO⟩ => ?_)
  refine WP.seq (WP.mono (chalHash_ok hL hc6) fun t7 ⟨hc7, f7, hC⟩ => ?_)
  refine WP.seq (WP.mono (red_ok hL hc7 (d := 256) (by omega) (by omega) (by omega)) fun t8 ⟨hc8, f8, hK⟩ => ?_)
  refine WP.seq (WP.mono (mulAdd_ok hL hc8) fun t9 ⟨hc9, f9, hM⟩ => ?_)
  refine WP.mono (wipe_ok hL hc9) fun t10 ⟨hc10, f10⟩ => ⟨hc10, ?_⟩
  -- Facts about the regions.
  have xS : ∀ {d n : Nat}, d + n ≤ 448 → Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ L.SCR :=
    fun h => fr_x hL h
  have rHW : ∀ {d n : Nat}, d + n ≤ 448 → (16 + 114 ≤ d) → ∀ r ∈ HW L,
      Region.Disjoint ⟨L.SP + BitVec.ofNat 64 d, n⟩ r := fun h h' r hr => by
    simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS h, ff L (.inr h') h (by omega), fb L h]
  have oHW : ∀ {e k : Nat}, e + k ≤ 114 → ∀ r ∈ HW L, Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ r :=
    fun h r hr => by
      simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [ox hL h, (fo hL (d := 16) (n := 114) (by omega) h).symm, ob hL h]
  have three : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → Region.Disjoint ⟨p, n⟩ L.SCR →
      Region.Disjoint ⟨p, n⟩ ⟨L.B, 16⟩ → ∀ r ∈ [q, L.SCR, ⟨L.B, 16⟩], Region.Disjoint ⟨p, n⟩ r :=
    fun h₁ h₂ h₃ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁, h₂, h₃]
  have one : ∀ {p : Addr} {n : Nat} {q : Region}, Region.Disjoint ⟨p, n⟩ q → ∀ r ∈ [q], Region.Disjoint ⟨p, n⟩ r :=
    fun h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h
  -- The header, through the hashes and the calls up to the challenge's hash.
  have hdr0 : ∀ r ∈ HW L, Region.Disjoint ⟨L.SP + BitVec.ofNat 64 0, 10⟩ r := fun r hr => by
    simp only [HW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [xS (by omega), ff L (.inl (by omega)) (by omega) (by omega), fb L (by omega)]
  rw [sp0] at hdr0
  have hx0 := xS (d := 0) (n := 10) (by omega); rw [sp0] at hx0
  have hb0 := fb L (d := 0) (n := 10) (by omega); rw [sp0] at hb0
  have e2 := keepB f2 hdr0 (by decide)
  have e3 := keepB f3 (one (q := ⟨L.S, 64⟩) (by
    have := ff L (d := 0) (n := 10) (e := 320) (k := 64) (.inl (by omega)) (by omega) (by omega)
    rwa [sp0] at this)) (by decide)
  have e4 := keepB f4 hdr0 (by decide)
  have e5 := keepB f5 (three (by
    have := ff L (d := 0) (n := 10) (e := 384) (k := 57) (.inl (by omega)) (by omega) (by omega)
    rwa [sp0] at this) hx0 hb0) (by decide)
  have e6 := keepB f6 (three (by
    have := fo hL (d := 0) (n := 10) (e := 0) (k := 57) (by omega) (by omega)
    rwa [sp0, out0] at this) hx0 hb0) (by decide)
  -- The prefix, through the pruning.
  have p3 := keepB f3 (one (q := ⟨L.S, 64⟩) (ff L (d := 73) (n := 57) (e := 320) (k := 64) (.inl (by omega))
    (by omega) (by omega))) (by decide)
  -- `R`, through the challenge's hash and its reduction, and the scalar product.
  have o1 : ∀ {e k : Nat}, e + k ≤ 114 → Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ L.SCR ∧
      Region.Disjoint ⟨L.out + BitVec.ofNat 64 e, k⟩ ⟨L.B, 16⟩ := fun h => ⟨ox hL h, ob hL h⟩
  have r7 := keepB f7 (p := L.out) (n := 57) (by have := oHW (e := 0) (k := 57) (by omega); rwa [out0] at this)
    (by decide)
  have r8 := keepB f8 (p := L.out) (n := 57) (three (by
      have := (fo hL (d := 256) (n := 57) (e := 0) (k := 57) (by omega) (by omega)).symm
      rwa [out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega)).1; rwa [out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega)).2; rwa [out0] at this)) (by decide)
  have r9 := keepB f9 (p := L.out) (n := 57) (three (by
      have := Offset.disjoint L.out (d := 0) (n := 57) (e := 57) (k := 57) (.inl (by omega)) (by omega) (by omega)
      rwa [out0] at this) (by have := (o1 (e := 0) (k := 57) (by omega)).1; rwa [out0] at this)
      (by have := (o1 (e := 0) (k := 57) (by omega)).2; rwa [out0] at this)) (by decide)
  have r10 := keepB f10 (p := L.out) (n := 57) (one (by
      have := (fo hL (d := 320) (n := 128) (e := 0) (k := 57) (by omega) (by omega)).symm
      rwa [out0] at this)) (by decide)
  have s10 := keepB f10 (p := L.out + BitVec.ofNat 64 57) (n := 57)
    (one (fo hL (d := 320) (n := 128) (e := 57) (k := 57) (by omega) (by omega)).symm) (by decide)
  -- `r` and `s`, through the code after them.
  have rr6 := keepB f6 (p := L.R) (n := 57) (three (fo hL (d := 384) (n := 57) (e := 0) (k := 57) (by omega)
    (by omega) |> fun h => by rwa [out0] at h) (xS (by omega)) (fb L (by omega))) (by decide)
  have rr7 := keepB f7 (p := L.R) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have rr8 := keepB f8 (p := L.R) (n := 57) (three (ff L (.inr (by omega)) (by omega) (by omega)) (xS (by omega))
    (fb L (by omega))) (by decide)
  have ss4 := keepB f4 (p := L.S) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have ss5 := keepB f5 (p := L.S) (n := 57) (three (ff L (.inl (by omega)) (by omega) (by omega)) (xS (by omega))
    (fb L (by omega))) (by decide)
  have ss6 := keepB f6 (p := L.S) (n := 57) (three (fo hL (d := 320) (n := 57) (e := 0) (k := 57) (by omega)
    (by omega) |> fun h => by rwa [out0] at h) (xS (by omega)) (fb L (by omega))) (by decide)
  have ss7 := keepB f7 (p := L.S) (n := 57) (rHW (by omega) (by omega)) (by decide)
  have ss8 := keepB f8 (p := L.S) (n := 57) (three (ff L (.inr (by omega)) (by omega) (by omega)) (xS (by omega))
    (fb L (by omega))) (by decide)
  -- The pieces.
  have pre : bytesAt t2.mem (L.SP + BitVec.ofNat 64 73) 57 = (bytesAt t2.mem L.H 114).drop 57 := by
    rw [bytes_drop, Lay.H, add_add L.SP 16 57]
  change Spec.Ed448.bytesAt t5.mem L.R 57 = _ at hR
  change Spec.Ed448.bytesAt t8.mem L.K 57 = _ at hK
  rw [ed_bytesAt] at hs hR hO hK hM hpk ⊢
  rw [bytes_split, r10, r9, r8, r7, s10, hM, rr8, rr7, rr6, hR, hK, hC, hN, ss8, ss7, ss6, ss5, ss4, e6, e5, e4,
    e3, p3, pre, e2, hh, hS, hO, hR, hN, e3, p3, pre, e2, hh, hS]
  rw [hS] at hs
  rw [hash_eq L _ _ _ (Verify.bytesAt_length _ _ _), hash_eq' L _ _ _ _ (Verify.bytesAt_length _ _ _)]
  exact Proof.Ed448.sign_pipeline _ _ _ _ _ hpk hs

end

/-! ## The frame -/

theorem push_slot (B : Addr) (j : Nat) (hj : j < 56) :
    B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * (j + 1)) =
      B + BitVec.ofNat 64 16 + BitVec.ofNat 64 (440 - 8 * j) := by
  rw [add_add, Offset.sub_ofNat_eq _ (a := 8 * (j + 1)) (b := 464) (by omega), BitVec.add_sub_cancel]
  congr 2; omega

theorem push_base (B : Addr) : B + BitVec.ofNat 64 464 - BitVec.ofNat 64 (8 * 56) = B + BitVec.ofNat 64 16 := by
  have := push_slot B 55 (by omega); simpa using this

theorem regs_length : regs.length = 56 := rfl

/-- After the push of the registers holding the arguments and 0: `Ctx`. -/
theorem entry_ctx {L : Lay} (hL : L.Ok) {s : State} (hsp : s.gpr .rsp = L.B + BitVec.ofNat 64 464)
    (hrd : s.rd = L.rd) (hwr : s.wr = L.wr) (h11 : s.gpr .r11 = L.scr) (hdi : s.gpr .rdi = L.out)
    (h10 : s.gpr .r10 = L.len) (h9 : s.gpr .r9 = L.msg) (h8 : s.gpr .r8 = L.ctxLen) (hcx : s.gpr .rcx = L.ctx)
    (hdx : s.gpr .rdx = L.pk) (hsi : s.gpr .rsi = L.seed) :
    Ctx L s.gpr s.mxcsr s.mem (pushed regs s) := by
  have hn : 8 * regs.length ≤ (s.gpr .rsp).toNat := by
    rw [hsp, regs_length, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := hL.nB
    rw [Nat.mod_eq_of_lt (a := 464) (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  obtain ⟨hf, hw⟩ := pushRegs_mem s regs (by decide) hn
  have slot : ∀ j (hj : j < 56), (pushed regs s).mem.readW (L.SP + BitVec.ofNat 64 (440 - 8 * j)) 64 =
      s.gpr (regs[j]'(by rw [regs_length]; omega)) := fun j hj => by
    rw [← hw j (by rw [regs_length]; omega), hsp, push_slot _ j hj]; rfl
  have base : s.gpr .rsp - BitVec.ofNat 64 (8 * regs.length) = L.SP := by
    rw [hsp, regs_length]; exact push_base L.B
  refine ⟨by simp [hrd], by rw [pushed_wr, base, hwr]; rfl, by rw [pushed_rsp, base], fun r _ hr' => pushed_gpr _ _ hr',
    by simp, (slot 30 (by omega)).trans hdx, (slot 29 (by omega)).trans hcx, (slot 28 (by omega)).trans h8,
    (slot 27 (by omega)).trans h9, (slot 26 (by omega)).trans h10, (slot 25 (by omega)).trans hdi,
    (slot 24 (by omega)).trans h11, (slot 38 (by omega)).trans hsi, ?_⟩
  show Frame [L.SCR, L.OUT, L.STK] s.mem (pushRegs s regs).mem
  refine Frame.sub hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨L.STK, by simp, ?_⟩
  rw [base, regs_length]
  exact Offset.sub_base _ (by omega)

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `len` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {s : State} (h : SPre s) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.mem = s.mem ∧ s2.mxcsr = s.mxcsr) ∧
        Keep [.r10, .r11, .rax] s s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨sArgs s, by simp [h.rd], ?_⟩
    rw [← add_add, ← stackArgAddr0]
    exact Offset.contains_base _ hd (by omega)
  refine WP.keep _ ?_ (by decide)
  have h8 := hin 0 (by omega)
  have h16 := hin 8 (by omega)
  simp only [Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  exact ⟨rfl, rfl⟩

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-! ## The function -/

theorem signCached_wp (hb : BaseOk) {s : State} (hpre : (Spec.Ed448.signCachedContract X86_64.abi 464).pre s) :
    WP isa signCached s fun s' =>
      abiPreserved s s' ∧ (Spec.Ed448.signCachedContract X86_64.abi 464).post s s' := by
  have h := sPre_of hpre
  have hL := slay_ok h
  unfold signCached
  refine WP.seq (WP.mono (signMov_ok h) fun s2 ⟨⟨h10, h11, hm2, hx2⟩, k2⟩ => ?_)
  have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => k2.gpr hr
  have hsp2 : s2.gpr .rsp = (slay s).B + BitVec.ofNat 64 464 := by rw [hg2 _ (by decide), slay_B]
  have hn : 8 * regs.length ≤ (s2.gpr .rsp).toNat := by
    rw [hg2 _ (by decide), regs_length]; have := h.sp; omega
  refine WP.frame (by decide) (by decide) (by decide) hn ?_
  have hc := entry_ctx hL hsp2 k2.2.1 k2.2.2 h11 (hg2 _ (by decide)) h10 (hg2 _ (by decide)) (hg2 _ (by decide))
    (hg2 _ (by decide)) (hg2 _ (by decide)) (hg2 _ (by decide))
  have hpk : Spec.Ed448.bytesAt s2.mem (slay s).pk 57 =
      Spec.Ed448.publicKey (Spec.Ed448.bytesAt s2.mem (slay s).seed 57) := by
    rw [hm2]; exact h.pk
  refine WP.mono (body_ok hb hL hc hpk) fun s' ⟨hc', hr⟩ => ⟨by rw [hc'.rsp, hc.rsp], by rw [hc'.wr, hc.wr], ?_, ?_⟩
  · -- The calling convention.
    refine ⟨fun r hr => ?_, ?_, ?_⟩
    · by_cases hr' : r = .rsp
      · subst hr'
        rw [popped_rsp, hc'.rsp, Lay.SP, add_add, regs_length, slay_B]
      · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hc'.cs r hr hr', hg2 r (cs_tmp r hr)]
    · have eR : sRet s = ⟨(slay s).B + BitVec.ofNat 64 464, 8⟩ := by rw [slay_B]
      rw [popped_mem, hc'.frame.readW (r := sRet s) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact h.retScr
          · exact h.retOut
          · rw [eR]; exact Offset.disjoint_base _ (by omega) (by have := hL.nB; omega)) (by decide), hm2]
    · rw [popped_mxcsr, hc'.mx, hx2]
  · sig_post [Spec.Ed448.signCachedContract, Spec.Ed448.signCachedSig, Spec.Ed448.scratchWords, X86_64.abi,
      X86_64.argRegs, List.range, List.range.loop]
    rw [hm2] at hr
    exact hr

end VG.Proof.Ed448.X86_64.SignCached
