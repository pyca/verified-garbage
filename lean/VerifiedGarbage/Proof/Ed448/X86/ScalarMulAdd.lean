import VerifiedGarbage.Proof.Ed448.X86.ScalarMain
import VerifiedGarbage.Proof.X448.X86.MulLoop

/-!
# Ed448 scalar multiply-add on x86 (32-bit): the steps

The inputs reduced (`reduceArg_ok`), the product of two with X448's rows
(`product_ok`), its limbs reduced (`reduceProduct_ok`), and the sum with the
third (`addPass_ok`), which `reduceT` reduces once more.
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.Radix16 VG.Proof.X448.X86 VG.Proof.Ed448.Limbs16
open VG.Impl.Ed448.X86 (W TF RA SK SS SR reduceArg product reduceProduct addSrc addPass)
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

theorem SK_eq : SK = 320 := rfl
theorem SS_eq : SS = 448 := rfl
theorem SR_eq : SR = 576 := rfl
theorem RA_eq : RA = 192 := rfl

/-! ## The inputs -/

/-- `reduceArg d o`: the remainder at `o` of the 57 bytes at the argument
`i` (at `[esp + 4 + 4 i]`). -/
theorem reduceArg_ok {s₀ s : State} {n sc : Nat} (hA : Args s₀ n sc) {base : Addr}
    (hbase : (arg s₀ sc).setWidth 64 = base) (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base)
    {i : Nat} (hi : i < n) {o : Nat} (ho : Buf o) (hin : Input s₀ base (arg s₀ i) 57) :
    WP isa (reduceArg (4 + 4 * i) o) s fun t =>
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t ∧ Outside2 base W 160 o 112 s.mem t.mem ∧
      Bounded t.mem base o ∧
      fe t.mem base o = decodeLE (bytesAt s₀.mem ((arg s₀ i).setWidth 64) 57) % L := by
  unfold reduceArg
  refine WP.seq (hA.load hsp hr hwr (hbase ▸ hm) hi fun u hu => WP.block_nil ?_)
  have hinu : Input u base (arg s₀ i) 57 :=
    ⟨hin.fit, by rw [hu.rd, hu.wr, hr, hwr]; exact hin.read, hin.far⟩
  refine WP.mono (reduce57_ok ho (hs.of_upd hu (by decide)) hu.gpr hinu) fun t ⟨kt, lt, vt⟩ =>
    ⟨(hu.rest (by decide)).trans (kt.regs.mono (by decide)), by rw [← hu.mem]; exact kt.mem, lt, ?_⟩
  rw [vt, hu.mem, hin.bytes hm]

/-! ## The product -/

theorem product_ok {s : State} {base : Addr} (hs : Scr s base) (hk : Bounded s.mem base SK)
    (hl : Bounded s.mem base SS) :
    WP isa product s fun t => Scr t base ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outside base Impl.X448.X86.ACC 224 s.mem t.mem ∧
      (∀ j < 56, limbs t.mem base Impl.X448.X86.ACC j < radix) ∧
      valN (limbs t.mem base Impl.X448.X86.ACC) 56 = fe s.mem base SK * fe s.mem base SS := by
  unfold product
  refine WP.seq (WP.mono (mulPre_ok hs SK SS) fun u hu => ?_)
  refine WP.mono (mulLoop_ok (by decide) (by decide) hk hl hu) fun t ht =>
    ⟨ht.scr, ht.regs, ht.mem, ht.lt, ht.val⟩

theorem reduceProduct_ok {s : State} {base : Addr} (hs : Scr s base)
    (hacc : ∀ j < 56, limbs s.mem base Impl.X448.X86.ACC j < radix) :
    WP isa reduceProduct s fun t => LoopKeep base RA s t ∧ Bounded t.mem base RA ∧
      fe t.mem base RA = valN (limbs s.mem base Impl.X448.X86.ACC) 56 % L := by
  have hA := ACC_eq
  have hR := RA_eq
  unfold reduceProduct
  have hinit : WP isa (.block (Impl.Ed448.X86.zeroR RA ++ ([.mov .ebp (.imm 224)] : List Instr))) s
      fun v => LoopKeep base RA s v ∧ v.gpr .ebp = BitVec.ofNat 32 (4 * 56) ∧
        Bounded v.mem base RA ∧ fe v.mem base RA = 0 := by
    rw [WP.block_append_iff]
    exact WP.mono (zeroR_ok (o := RA) (by decide) hs) fun u ⟨ku, fu, zu⟩ =>
      wp_mov rfl fun v hv => WP.block_nil
        ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by
          rw [hv.mem]; exact fun p _ h2 => fu p h2⟩,
          hv.gpr, by rw [hv.mem]; exact Bounded_zero zu, by rw [hv.mem]; exact fe_zero zu⟩
  refine WP.seq (WP.mono hinit fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have la : ∀ j < 56, limbs v.mem base Impl.X448.X86.ACC j = limbs s.mem base Impl.X448.X86.ACC j :=
    fun j hj => congrArg BitVec.toNat (kv.mem.word (Or.inr (by simp only [W]; omega))
      (Or.inr (by omega)) (by omega))
  refine WP.mono (limbLoop_ok (hs.of_keeps kv.regs (by decide))
    (fun j hj => by rw [la j hj]; exact hacc j hj) cv lv vv) fun t ⟨kt, lt, vt⟩ =>
    ⟨kv.trans kt, lt, by rw [vt, valN_congr la]⟩

/-! ## The sum -/

theorem addPass_ok {s : State} {base : Addr} (hs : Scr s base)
    (ha : Bounded s.mem base RA) (hr : Bounded s.mem base SR)
    (hva : fe s.mem base RA < L) (hvr : fe s.mem base SR < L) :
    WP isa (.block addPass) s fun t => Keeps [.eax, .ebx, .edx] s t ∧
      Outside base TF 112 s.mem t.mem ∧ Bounded t.mem base TF ∧
      fe t.mem base TF = fe s.mem base RA + fe s.mem base SR := by
  have hT := TF_eq
  have hR := RA_eq
  have hS := SR_eq
  unfold addPass
  rw [WP.block_append_iff]
  refine WP.mono (zeroCarry_ok s) fun s1 ⟨e1, m1, k1⟩ => ?_
  have hs1 := hs.of_keeps k1 (by decide)
  refine WP.mono (carryPass_ok (rb := .edi) (o := TF) (d := TF) (s0 := s1)
    (c := fun k => limbs s.mem base RA k + limbs s.mem base SR k) (by decide) (by omega)
    (fun k hk => hs1.ea (by omega)) (fun k hk => hs1.write (by omega)) (by rw [e1]; rfl)
    (fun k hk => by have := ha k hk; have := hr k hk; simp only [radix] at *; omega) ?_)
    fun t ht => ?_
  · intro k hk s' hp
    have hs' := hs1.of_keeps hp.regs (by decide)
    have hm := hp.mem
    rw [m1] at hm
    have e1 : limbs s'.mem base RA k = limbs s.mem base RA k :=
      hm.limbs (Or.inr (by omega)) (by omega) hk
    have e2 : limbs s'.mem base SR k = limbs s.mem base SR k :=
      hm.limbs (Or.inr (by omega)) (by omega) hk
    unfold addSrc
    refine load_ok hs' (by omega) fun v1 w1 => ?_
    refine wp_alu (Or.inl rfl) (readSc (hs'.of_upd w1 (by decide)) (by omega)) fun v2 w2 _ =>
      WP.block_nil ⟨?_, (w1.rest (by decide)).trans (w2.rest (by decide)), by rw [w2.mem, w1.mem]⟩
    have x1 : (v1.gpr .eax).toNat = limbs s.mem base RA k := by rw [w1.gpr]; exact e1
    have x2 : (word v1.mem base (SR + 4 * k)).toNat = limbs s.mem base SR k := by
      rw [w1.mem]; exact e2
    rw [w2.gpr]
    change (v1.gpr .eax + word v1.mem base (SR + 4 * k)).toNat = _
    rw [toNat_add_lt (by rw [x1, x2]; have := ha k hk; have := hr k hk; simp only [radix] at *; omega),
      x1, x2]
  · generalize hcf : (fun k => limbs s.mem base RA k + limbs s.mem base SR k) = c at ht
    have hcv : valN c 28 = fe s.mem base RA + fe s.mem base SR := by rw [← hcf, valN_add]
    have hlt : valN c 28 < radix ^ 28 := by
      have := two_L_le
      rw [hcv]; omega
    refine ⟨(k1.mono (by decide)).trans ht.regs, by rw [← m1]; exact ht.mem,
      fun k hk => by rw [ht.outs k hk]; exact digit_lt _ _, ?_⟩
    show valN (limbs t.mem base TF) 28 = _
    rw [valN_congr ht.outs, digits_val hlt, hcv]

end VG.Proof.Ed448.X86
