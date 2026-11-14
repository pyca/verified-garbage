module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.SignCtx
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Sign
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Encode
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.VerifyCorrect

/-! ### `RsaPkcs1Sig.X86_64.SignFrame`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, below which the
call of `vg_rsa_private_checked` uses 3264 bytes; its slots, and the
function's stack arguments, at `S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_using []

/-! ## The precondition, by name -/

/-- `sigContract.pre`, by name. -/
structure PreS (s : State) : Prop where
  sp1 : sigStack ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 128 ≤ 2 ^ 64
  hrd : ∀ r ∈ ([⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 1, (stackArg s 2).toNat⟩, ⟨stackArg s 3, (stackArg s 4).toNat⟩,
    ⟨stackArg s 5, (stackArg s 6).toNat⟩, ⟨stackArg s 7, (stackArg s 8).toNat⟩,
    ⟨stackArg s 9, (stackArg s 10).toNat⟩, ⟨stackArg s 11, (stackArg s 12).toNat⟩] : List Region), r ∈ s.rd
  /-- The stack arguments, in a readable region of at least 120 bytes. -/
  hra : ∃ A, 120 ≤ A ∧ A < 2 ^ 32 ∧ (⟨stackArgAddr s 0, A⟩ : Region) ∈ s.rd
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOd : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dds : (⟨stackArg s 1, (stackArg s 2).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dps : (⟨stackArg s 3, (stackArg s 4).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqs : (⟨stackArg s 5, (stackArg s 6).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddps : (⟨stackArg s 7, (stackArg s 8).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  ddqs : (⟨stackArg s 9, (stackArg s 10).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dqis : (⟨stackArg s 11, (stackArg s 12).toNat⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dsa : (⟨stackArg s 13, (stackArg s 14).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKd : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 1, (stackArg s 2).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 3, (stackArg s 4).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 5, (stackArg s 6).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 7, (stackArg s 8).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 9, (stackArg s 10).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 11, (stackArg s 12).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint
    ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 sigStack, sigStack⟩ : Region).Disjoint ⟨stackArgAddr s 0, 120⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wD : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  wP : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 64
  wQ : (stackArg s 5).toNat + (stackArg s 6).toNat ≤ 2 ^ 64
  wDp : (stackArg s 7).toNat + (stackArg s 8).toNat ≤ 2 ^ 64
  wDq : (stackArg s 9).toNat + (stackArg s 10).toNat ≤ 2 ^ 64
  wQi : (stackArg s 11).toNat + (stackArg s 12).toNat ≤ 2 ^ 64
  wS : (stackArg s 13).toNat + (stackArg s 14).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 4).toNat
  pl2 : (stackArg s 4).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 6).toNat
  ql2 : (stackArg s 6).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 8).toNat = (stackArg s 4).toNat
  hqil : (stackArg s 12).toNat = (stackArg s 4).toNat
  hdql : (stackArg s 10).toNat = (stackArg s 6).toNat
  hsl : 16 * (s.gpr .rcx).toNat + 32 ≤ (stackArg s 14).toNat

/-! ## The frame -/

abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 sigStack

def stkR (s : State) : Region := ⟨kb s, sigStack⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 13, (stackArg s 14).toNat * 8⟩

/-- The frame's base, from the stack's: `frameBytes` above it, below which
the call uses `sigStack - frameBytes` bytes. -/
theorem fb_eq (s : State) : fb s = off (kb s) (sigStack - frameBytes) :=
  Offset.sub_ofNat_eq _ (by decide)

theorem kb_toNat {s : State} (hp : PreS s) : (kb s).toNat + sigStack + 128 ≤ 2 ^ 64 ∧
    (kb s).toNat + sigStack = (s.gpr .rsp).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold sigStack at *; omega_arith

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]

theorem fb_toNat {s : State} (hp : PreS s) : (fb s).toNat + frameBytes + 8 + 120 ≤ 2 ^ 64 ∧
    (fb s).toNat = (kb s).toNat + (sigStack - frameBytes) := by
  have ⟨h1, h2⟩ := kb_toNat hp
  rw [fb_eq, toNat_off (by unfold sigStack frameBytes at *; omega_using [h1])]
  unfold frameBytes sigStack at *; omega_using [h1]

theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold sigStack frameBytes; omega_using [h])

theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega_using [hlt]
  have := frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- In the frame, from the entry state `s`: with the arguments kept in
their slots, memory changed only where the function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sOl : word t.mem (fb s) oOl = s.gpr .rsi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

/-- `Env` but for the slots of `out` and `out_len`, which the call of
`vg_rsa_private_checked_precomputed` takes for its stack arguments; nothing
reads them after it. -/
structure EnvC (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.core {s t : State} (h : Env s t) : EnvC s t :=
  ⟨h.rsp, h.rd, h.wr, h.mem, h.sN, h.sK, h.sE, h.sEl⟩

theorem EnvC.scr {s t : State} (h : EnvC s t) (hp : PreS s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

theorem Env.scr {s t : State} (h : Env s t) (hp : PreS s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by have := fb_toNat hp; omega_using [this])

theorem bytes_of_frame {s : State} {m : Mem} (hf : Frame [stkR s, outR s, scrR s] s.mem m) {p : Addr} {len : Nat}
    (hk : (stkR s).Disjoint ⟨p, len⟩) (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩)
    (hl : len ≤ 2 ^ 64) : Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega_using [], BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

theorem arg_outside {s : State} (hp : PreS s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 15) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega_using [])) (by unfold frameBytes at *; omega_using [hj])

theorem Env.arg {s t : State} (h : Env s t) (hp : PreS s) {j : Nat} (hj : j < 15) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 120⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem arg_in {s t : State} (hp : PreS s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 15) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  obtain ⟨A, hA, hA', hm⟩ := hp.hra
  exact ⟨⟨stackArgAddr s 0, A⟩, List.mem_append_left _ (by rw [hrd]; exact hm),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_using [hj, hA]) (by omega_using [hj])⟩

theorem arg_ea {s t : State} (h : t.gpr .rsp = fb s) (j : Nat) : t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, stackArgAddr_fb]

theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega_using [hd])).word (by omega_using [h]) (by omega_using [hd'])

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn

end

end

/-!
# `vg_rsa_pkcs1_sign` on x86-64: the blocks around the encoding and the call

The frame's push, the slots and the arguments of `encode` (`head_ok`, and
`encPre`, what `encode` needs), the zeros to `out` if it fails
(`zeroSlots_ok`), the arguments of `vg_rsa_private_checked` (`callArgs_ok`),
and the zeros to `EM` after the call (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86_64.Sgn

open VG VG.X86_64 VG.Impl.RsaPkcs1Sig.X86_64 VG.Impl.RsaPkcs1Sig.X86_64.Sign
open VG.Impl.RsaPkcs1Sig.X86_64.Verify (sp lea)
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaPkcs1Sig.X86_64 VG.WriteBytes

/-! ## Memory in the frame -/

/-- `Env` past changes of the registers but `rsp`, and of memory in the
frame outside its slots or in `out`. -/
theorem Env.of {s t u : State} (he : Env s t) (hp : PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ (d + n ≤ oOut ∨ oEM ≤ d) ∧ d + n ≤ frameBytes) ∨
      r = outR s) : Env s u := by
  have hsl : ∀ {d}, oOut ≤ d → d + 8 ≤ oEM → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold oOut oEM at *; omega_arith) (by unfold frameBytes oEM at *; omega_arith)
          (by unfold frameBytes at *; omega_arith)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM frameBytes at *; omega_arith)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sOut, (hsl (by decide) (by decide)).trans he.sOl,
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `Env` past changes of the registers but `rsp`. -/
theorem Env.regs {s t u : State} (he : Env s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : Env s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sOut, hm ▸ he.sOl, hm ▸ he.sN,
    hm ▸ he.sK, hm ▸ he.sE, hm ▸ he.sEl⟩

/-- `EnvC` past changes of the registers but `rsp`, and of memory in the
frame outside its slots from `n`'s or in `out`. -/
theorem EnvC.of {s t u : State} (he : EnvC s t) (hp : PreS s) (hsp : u.gpr .rsp = t.gpr .rsp) (hrd : u.rd = t.rd)
    (hwr : u.wr = t.wr) {rs : List Region} (hf : Frame rs t.mem u.mem)
    (hs : ∀ r ∈ rs, (∃ d n, r = ⟨off (fb s) d, n⟩ ∧ (d + n ≤ oN ∨ oEM ≤ d) ∧ d + n ≤ frameBytes) ∨
      r = outR s) : EnvC s u := by
  have hsl : ∀ {d}, oN ≤ d → d + 8 ≤ oEM → word u.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      rcases hs r hr with ⟨d', n, rfl, h₁, h₂⟩ | rfl
      · exact Offset.disjoint _ (by unfold oN oEM at *; omega_arith) (by unfold frameBytes oEM at *; omega_arith)
          (by unfold frameBytes at *; omega_arith)
      · exact (hp.dKo.sub_left (frame_sub s (by unfold oEM frameBytes at *; omega_arith)))) (by decide)
  refine ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, he.mem.trans (hf.sub fun r hr => ?_),
    (hsl (by decide) (by decide)).trans he.sN, (hsl (by decide) (by decide)).trans he.sK,
    (hsl (by decide) (by decide)).trans he.sE, (hsl (by decide) (by decide)).trans he.sEl⟩
  rcases hs r hr with ⟨d, n, rfl, -, h₂⟩ | rfl
  · exact ⟨_, List.mem_cons_self .., frame_sub s h₂⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩

/-- `EnvC` past changes of the registers but `rsp`. -/
theorem EnvC.regs {s t u : State} (he : EnvC s t) (hsp : u.gpr .rsp = t.gpr .rsp) (hm : u.mem = t.mem)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) : EnvC s u :=
  ⟨hsp.trans he.rsp, hrd.trans he.rd, hwr.trans he.wr, hm ▸ he.mem, hm ▸ he.sN, hm ▸ he.sK, hm ▸ he.sE,
    hm ▸ he.sEl⟩

theorem frame_bytes {s : State} {d n : Nat} (hp : PreS s) (h : d + n ≤ frameBytes) :
    ∀ i < n, InRegions (⟨fb s, frameBytes⟩ :: s.wr) (off (fb s) d + BitVec.ofNat 64 i) 1 := by
  have := fb_toNat hp
  intro i hi
  refine ⟨_, List.mem_cons_self .., ?_⟩
  rw [show off (fb s) d + BitVec.ofNat 64 i = off (fb s) (d + i) from off_off _ _ _]
  exact Offset.contains_base _ (by omega_arith) (by unfold frameBytes at *; omega_arith)

/-! ## The head -/

/-- The frame's push, the slots and the arguments of `encode`. -/
theorem head_ok {s : State} (hp : PreS s) :
    WP isa (.block (slotStores ++ encArgs)) (allocState frameBytes s) fun t => Env s t ∧
      t.gpr .r8 = off (fb s) oEM ∧ t.gpr .rcx = s.gpr .rcx ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2 ∧ (∀ r ∈ calleeSaved, r ≠ .rsp → t.gpr r = s.gpr r) := by
  have hF := fb_toNat hp
  let A := allocState frameBytes s
  try rewrite [show allocState frameBytes s = A from rfl] at *
  have hA : A = allocState frameBytes s := rfl
  have hsp : A.gpr .rsp = fb s := rfl
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by omega_arith)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem =
      (((((s.mem.writeW (off (fb s) oOut) (s.gpr .rdi)).writeW (off (fb s) oOl) (s.gpr .rsi)).writeW
        (off (fb s) oN) (s.gpr .rdx)).writeW (off (fb s) oK) (s.gpr .rcx)).writeW (off (fb s) oE)
        (s.gpr .r8)).writeW (off (fb s) oEl) (s.gpr .r9)) (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oOl) (by decide),
      hs.st (d := oN) (by decide), hs.st (d := oK) (by decide), hs.st (d := oE) (by decide),
      hs.st (d := oEl) (by decide)]
    rfl) rfl) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega_arith
    unfold frameBytes at hx hx'
    simp only [oOut, oOl, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith),
      writeW_outside _ _ _ (by omega_arith) x (by omega_arith), writeW_outside _ _ _ (by omega_arith) x (by omega_arith)]
  have hslots : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oOl = s.gpr .rsi ∧
      word t₁.mem (fb s) oN = s.gpr .rdx ∧ word t₁.mem (fb s) oK = s.gpr .rcx ∧
      word t₁.mem (fb s) oE = s.gpr .r8 ∧ word t₁.mem (fb s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oOl, oN, oK, oE, oEl, and_self]
  have hsp₁ : t₁.gpr .rsp = fb s := (k₁.gpr (by decide)).trans hsp
  have hrd : t₁.rd = s.rd := k₁.2.1
  have g : ∀ r, r ≠ .rsp → t₁.gpr r = s.gpr r := fun r h => by
    rw [k₁.gpr (by simp)]; simp [hA, allocState_gpr, h]
  refine WP.mono (WP.keep [.r8, .rdx, .rsi, .r9] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r8 = off (fb s) oEM ∧
      t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64 ∧ t.gpr .rsi = stackArg s 1 ∧
      t.gpr .r9 = stackArg s 2) (by
    xrun [encArgs, lea, List.cons_append, List.nil_append, @arg_ea s, ea_sp, hsp₁,
      sx_ofNat (show oEM < 2 ^ 31 by decide), arg_in hp hrd (show 0 < 15 by decide),
      arg_in hp hrd (show 1 < 15 by decide), arg_in hp hrd (show 2 < 15 by decide),
      arg_outside hp ho₁ (show 0 < 15 by decide), arg_outside hp ho₁ (show 1 < 15 by decide),
      arg_outside hp ho₁ (show 2 < 15 by decide)]) rfl) fun t ⟨⟨hm, h8, hdx, hsi, h9⟩, k⟩ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hslots
  refine ⟨⟨(k.gpr (by decide)).trans hsp₁, k.2.1.trans hrd, k.2.2.trans k₁.2.2, frame_of_outside (hm ▸ ho₁),
    hm ▸ h1, hm ▸ h2, hm ▸ h3, hm ▸ h4, hm ▸ h5, hm ▸ h6⟩, h8, by rw [k.gpr (by decide), g _ (by decide)],
    hdx, hsi, h9, fun r hr hr' => ?_⟩
  rw [k.gpr (by simp [calleeSaved] at hr ⊢; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | simp_all),
    g r hr']

/-- What `encode` needs, from the head. -/
theorem encPre {s t : State} (hp : PreS s) (he : Env s t) (h8 : t.gpr .r8 = off (fb s) oEM)
    (hcx : t.gpr .rcx = s.gpr .rcx) (hdx : t.gpr .rdx = ((stackArg s 0).setWidth 32).setWidth 64)
    (hsi : t.gpr .rsi = stackArg s 1) (h9 : t.gpr .r9 = stackArg s 2) :
    EPre t ((stackArg s 0).setWidth 32) (s.gpr .rcx).toNat := by
  have hk2 := hp.k2
  have hdl := hp.wD
  have sEM : Region.Sub ⟨off (fb s) oEM, (s.gpr .rcx).toNat⟩ (stkR s) :=
    frame_sub s (by unfold oEM frameBytes; omega_arith)
  exact {
    rdx := by rw [hdx]; apply BitVec.eq_of_toNat_eq; simp
    hk := by rw [hcx]
    kle := hk2
    buf := fun i hi => by rw [h8, he.wr]; exact frame_bytes hp (by unfold oEM frameBytes; omega_arith) i hi
    rd := fun j hj => by
      rw [hsi, he.rd, he.wr]
      rw [h9] at hj
      exact ⟨⟨stackArg s 1, (stackArg s 2).toNat⟩, List.mem_append_left _ (hp.hrd _ (by simp)),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
    sep := fun j hj i hi => by
      rw [hsi, h8]
      rw [h9] at hj
      exact ne_of_disjoint (hp.dKd.sub_left sEM).symm (by omega_arith) (by omega_arith) hj hi }

/-! ## Zeros to `out` -/

/-- The address and length of `out`, from their slots. -/
theorem zeroHead_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block [.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl))]) t
      fun u => Keep [.rdi, .rsi] t u ∧ u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun u => u.mem = t.mem ∧ u.gpr .rdi = s.gpr .rdi ∧
      u.gpr .rsi = s.gpr .rsi) (by
    xrun [ea_sp, he.rsp, hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), he.sOut, he.sOl]) rfl)
    fun u ⟨h, k⟩ => ⟨k, h⟩

theorem zeroSlots_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa zeroSlots t fun u => Env s u ∧ (u.gpr .rax).setWidth 32 = 0 ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsiK := hp.hsi
  unfold zeroSlots
  refine WP.seq (WP.mono (zeroHead_ok hp he) fun t₁ ⟨k₁, hm₁, hdi, hsi⟩ => ?_)
  have hwr : outR s ∈ t₁.wr := by rw [k₁.2.2, he.wr, hp.hwr]; simp [outR]
  refine WP.mono (Rec.zeroOut_ok (n := (s.gpr .rsi).toNat) (by omega_arith) (by omega_arith)
    (by rw [hsi, Rec.ofNat_toNat64]) (by
      rw [hdi]; intro i hi; exact ⟨_, hwr, Offset.contains_base _ (by have := hp.wO; omega_arith) (by omega_arith)⟩))
    fun u ⟨hK, hm, hax⟩ => ⟨?_, by rw [hax]; rfl, ?_⟩
  · refine Env.of (he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2) hp (hK.gpr (by decide)) hK.2.1 hK.2.2
      (hm ▸ frame_writeBytes _ _ _) fun r hr => .inr ?_
    rw [List.mem_singleton.mp hr, hdi, List.length_replicate]; rfl
  · rw [hm, hdi, ← hsiK]
    have := bytesAt_writeBytes t₁.mem (s.gpr .rdi) (List.replicate (s.gpr .rsi).toNat 0) (by simp; omega_arith)
    rwa [List.length_replicate] at this

/-! ## The arguments of the call -/

/-- The call's stack argument `i`: `EM`, `n_len`, then the function's stack
arguments from `p` on. -/
def callArg (s : State) : Nat → BitVec 64
  | 0 => off (fb s) oEM
  | 1 => s.gpr .rcx
  | i + 2 => stackArg s (i + 3)

/-- Stack argument `j + 3` to the frame's word `j + 2`. -/
theorem copyArg_ok {s t : State} (hp : PreS s) (he : Env s t) {j : Nat} (hj : j < 12) :
    WP isa (.block (copyArg j)) t fun t' => Env s t' ∧
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3)) ∧ Keep [.rax] t t' := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.rax] (Q := fun t' =>
      t'.mem = t.mem.writeW (off (fb s) (8 * (j + 2))) (stackArg s (j + 3))) (by
    xrun [copyArg, @arg_ea s, ea_sp, he.rsp, arg_in hp he.rd (show j + 3 < 15 by omega_arith),
      he.arg hp (show j + 3 < 15 by omega_arith), hs.st (d := 8 * (j + 2)) (by unfold frameBytes; omega_arith)]) rfl)
    fun t' ⟨hm, k⟩ => ⟨Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 (hm ▸ (Frame.refl _ _).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
      ⟨8 * (j + 2), 8, List.mem_singleton.mp hr, .inl (by unfold oOut; omega_arith), by unfold frameBytes; omega_arith⟩, hm, k⟩

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : PreS s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), Env s t →
    WP isa (.block ((List.range n).flatMap copyArg)) t fun t' => Env s t' ∧
      (∀ i < n, word t'.mem (fb s) (8 * (i + 2)) = stackArg s (i + 3)) ∧
      (∀ d, d + 8 ≤ 16 ∨ 16 + 8 * n ≤ d → d + 8 ≤ frameBytes → word t'.mem (fb s) d = word t.mem (fb s) d) ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax] t t'
  | 0, _, t, he => WP.block_nil ⟨he, fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Frame.refl _ _,
      Keep.refl _ _⟩
  | n + 1, hn, t, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copies_ok hp n (by omega_arith) t he) fun t₁ ⟨he₁, hw₁, hk₁, hf₁, k₁⟩ => ?_
    refine WP.mono (copyArg_ok hp he₁ (show n < 12 by omega_arith)) fun t' ⟨he', hm, k'⟩ =>
      ⟨he', fun i hi => ?_, fun d hd hd' => ?_, hf₁.trans (hm ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Offset.contains_base (fb s) (d := 8 * (n + 2)) (n := 8) (k := 112)
          (by omega_arith) (by omega_arith))), (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [word_wo _ _ _ (.inr (by omega_arith)) (by unfold frameBytes at *; omega_arith) (by unfold frameBytes at *; omega_arith)]
        exact hw₁ i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm, word_wo _ _ _ (by omega_arith) (by unfold frameBytes at *; omega_arith) (by unfold frameBytes at *; omega_arith)]
      exact hk₁ d (by omega_arith) hd'

theorem callArgs_eq : callArgs =
    (([.mov .rdi (.mem (sp oOut)), .mov .rsi (.mem (sp oOl)), .mov .rdx (.mem (sp oN)), .mov .rcx (.mem (sp oK)),
      .mov .r8 (.mem (sp oE)), .mov .r9 (.mem (sp oEl))] : List Instr) ++ lea .rax oEM ++
      ([.store (sp 0) .rax, .store (sp 8) .rcx] : List Instr)) ++ (List.range 12).flatMap copyArg := by
  simp only [callArgs, List.append_assoc]

/-- The arguments of `vg_rsa_private_checked`. -/
theorem callArgs_ok {s t : State} (hp : PreS s) (he : Env s t) :
    WP isa (.block callArgs) t fun t' => Env s t' ∧ (∀ i < 14, word t'.mem (fb s) (8 * i) = callArg s i) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = s.gpr .rsi ∧ t'.gpr .rdx = s.gpr .rdx ∧
      t'.gpr .rcx = s.gpr .rcx ∧ t'.gpr .r8 = s.gpr .r8 ∧ t'.gpr .r9 = s.gpr .r9 ∧
      Frame [⟨fb s, 112⟩] t.mem t'.mem ∧ Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t t' := by
  have hs := he.scr hp
  have h0 : InRegions t.wr (fb s) 8 := by
    simpa only [off, BitVec.add_zero] using hs.st (d := 0) (by decide)
  rw [callArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] (Q := fun u =>
      u.mem = (t.mem.writeW (fb s) (off (fb s) oEM)).writeW (off (fb s) 8) (s.gpr .rcx) ∧
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
      u.gpr .rcx = s.gpr .rcx ∧ u.gpr .r8 = s.gpr .r8 ∧ u.gpr .r9 = s.gpr .r9) (by
    have h8 : InRegions t.wr (fb s + 8) 8 := hs.st (d := 8) (by decide)
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, h0, h8, hs.st (d := 8) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oOl) (by decide), hs.ld (d := oN) (by decide),
      hs.ld (d := oK) (by decide), hs.ld (d := oE) (by decide), hs.ld (d := oEl) (by decide),
      he.sOut, he.sOl, he.sN, he.sK, he.sE, he.sEl, sx_ofNat (show oEM < 2 ^ 31 by decide)]) rfl) fun u ⟨⟨hm, hdi, hsi, hdx, hcx, h8, h9⟩, k⟩ => ?_
  have f : Frame [⟨fb s, 64 / 8⟩, ⟨off (fb s) 8, 64 / 8⟩] t.mem u.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have f' : Frame [⟨fb s, 112⟩] t.mem u.mem := f.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, Offset.sub_base (fb s) (d := 8) (n := 8) (k := 112) (by decide)⟩
  have heu : Env s u := by
    refine Env.of he hp (k.gpr (by decide)) k.2.1 k.2.2 f fun r hr => .inl ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨0, 8, by simp [off], .inl (by decide), by decide⟩
    · exact ⟨8, 8, rfl, .inl (by decide), by decide⟩
  refine WP.mono (copies_ok hp 12 (Nat.le_refl _) u heu) fun t' ⟨he', hw, hk, hf', k'⟩ =>
    ⟨he', fun i hi => ?_, by rw [k'.gpr (by decide), hdi], by rw [k'.gpr (by decide), hsi],
      by rw [k'.gpr (by decide), hdx], by rw [k'.gpr (by decide), hcx], by rw [k'.gpr (by decide), h8],
      by rw [k'.gpr (by decide), h9], f'.trans hf', (k.trans k').mono (by decide)⟩
  match i, hi with
  | 0, _ =>
    rw [hk 0 (.inl (by decide)) (by decide), hm]
    have := word_wo (t.mem.writeW (fb s) (off (fb s) oEM)) (fb s) (d := 8) (d' := 0) (s.gpr .rcx)
      (.inr (by decide)) (by decide) (by decide)
    rw [this]; exact Ver.word_self0 _ _ _
  | 1, _ =>
    rw [hk 8 (.inl (by decide)) (by decide), hm]; exact word_writeW_self _ _ _ _
  | i + 2, hi => exact hw i (by omega_arith)

/-- The count and address of `EM`'s bytes, and the zero byte. -/
theorem wipeHead_ok {s t : State} (hp : PreS s) (he : EnvC s t) :
    WP isa (.block (([.mov .r11 (.mem (sp oK)), .mov32 .rdx (.imm 0)] : List Instr) ++ lea .r10 oEM)) t fun u =>
      Keep [.r11, .rdx, .r10] t u ∧ u.mem = t.mem ∧ u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧
      u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM := by
  have hs := he.scr hp
  refine WP.mono (WP.keep [.r11, .rdx, .r10] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r11 = BitVec.ofNat 64 (s.gpr .rcx).toNat ∧ u.gpr .rdx = 0 ∧ u.gpr .r10 = off (fb s) oEM) (by
    xrun [lea, List.cons_append, List.nil_append, ea_sp, he.rsp, hs.ld (d := oK) (by decide), he.sK,
      sx_ofNat (show oEM < 2 ^ 31 by decide), Rec.ofNat_toNat64]) rfl) fun u ⟨h, k⟩ => ⟨k, h⟩

/-- `EM` overwritten with zeros, keeping `rax`. -/
theorem wipe_ok {s t : State} (hp : PreS s) (he : EnvC s t) :
    WP isa wipe t fun u => EnvC s u ∧ u.gpr .rax = t.gpr .rax ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .rdi) (s.gpr .rcx).toNat = Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat := by
  have hs := he.scr hp
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hF := fb_toNat hp
  unfold wipe
  refine WP.seq (WP.mono (wipeHead_ok hp he) fun t₁ ⟨k₁, hm₁, h11, hdx, h10⟩ => ?_)
  have he₁ : EnvC s t₁ := he.regs (k₁.gpr (by decide)) hm₁ k₁.2.1 k₁.2.2
  refine wp_countdown (cnt := .r11) (N := (s.gpr .rcx).toNat) (by omega_arith) (by omega_arith)
    (fun i u => EnvC s u ∧ Keep [.r11, .rdx, .r10] t₁ u ∧ u.gpr .rdx = 0 ∧
      u.gpr .r10 = off (fb s) (oEM + i) ∧
      u.mem = writeBytes t₁.mem (off (fb s) oEM) (List.replicate i 0)) ?_ (fun u ⟨heu, ku, _, _, hmu⟩ => ?_)
    ⟨he₁, Keep.refl _ _, hdx, by rw [h10]; rfl, by simp only [List.replicate_zero, writeBytes_nil]⟩ h11
  · intro i hi u ⟨heu, ku, hdxu, h10u, hmu⟩ _
    have hA : InRegions u.wr (u.gpr .r10) 1 := by
      rw [h10u, heu.wr]
      obtain ⟨r, h, c⟩ := frame_bytes hp (d := oEM + i) (n := 1) (by unfold oEM frameBytes; omega_arith) 0 (by decide)
      exact ⟨r, h, by simpa only [BitVec.add_zero, off] using c⟩
    refine WP.mono (WP.keep [.r10, .r11] (Q := fun u' => u'.mem = u.mem.writeW (u.gpr .r10) (0 : Byte) ∧
        u'.gpr .r10 = u.gpr .r10 + 1 ∧ u'.gpr .r11 = u.gpr .r11 - 1 ∧ u'.zf = some (u.gpr .r11 - 1 == 0)) (by
      xrun [ea0, hA, hdxu]; rfl) rfl) fun u' ⟨⟨hm', h10', h11', hz⟩, k'⟩ => ⟨⟨?_, (ku.trans k').mono (by simp),
        by rw [k'.gpr (by decide), hdxu], ?_, ?_⟩, h11', hz⟩
    · refine EnvC.of heu hp (k'.gpr (by decide)) k'.2.1 k'.2.2 (hm' ▸ (Frame.refl _ _).writeW
        (List.mem_singleton_self _) _ (Region.contains_self _ _)) fun r hr => .inl
        ⟨oEM + i, 1, by rw [List.mem_singleton.mp hr, h10u], .inr (by unfold oEM; omega_arith),
          by unfold oEM frameBytes; omega_arith⟩
    · rw [h10', h10u]; exact off_off _ _ _
    · rw [hm', hmu, h10u, List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega_arith), List.length_replicate,
        show off (fb s) oEM + BitVec.ofNat 64 i = off (fb s) (oEM + i) from off_off _ _ _]
  · refine ⟨heu, ku.gpr (by decide) |>.trans (k₁.gpr (by decide)), ?_⟩
    rw [hmu, hm₁]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => (frame_writeBytes t.mem _ _).bytes (R := ⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩)
      (fun r hr => ?_) (by dsimp only; omega_arith) (List.mem_range.mp hi)
    rw [List.mem_singleton.mp hr, List.length_replicate]
    have h := hp.dKo.sub_left (frame_sub s (d := oEM) (n := (s.gpr .rcx).toNat)
      (by unfold oEM frameBytes; omega_arith))
    rw [hp.hsi] at h
    exact h.symm

end VG.Proof.RsaPkcs1Sig.X86_64.Sgn
