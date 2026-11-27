module

public import VerifiedGarbage.Proof.Rsa.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivFrame
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Rsa.Scratch
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
public import VerifiedGarbage.Proof.Rsa.X86_64.PublicImpl
public import VerifiedGarbage.Proof.Rsa.X86_64.PrivImpl

/-! ### `Rsa.X86_64.PrivPd`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.PrivCrt`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on x86-64: the call of the CRT

The CRT runs with the stack arguments the frame holds at `rsp`, writing
`M` at `oM` (`crt_pre`), and returns with `M` written and the frame's
slots kept (`crt_call`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The return address of a call from the frame. -/
abbrev kb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 (frameBytes + 8)

theorem fb_sub8 (s : State) : fb s - 8 = kb s := by
  simp only [fb, kb, BitVec.sub_sub]; rfl

theorem fb_kb (s : State) : fb s = kb s + BitVec.ofNat 64 8 := by
  rw [← fb_sub8]; exact (BitVec.sub_add_cancel _ _).symm

theorem fb_off (s : State) (d : Nat) : off (fb s) d = kb s + BitVec.ofNat 64 (8 + d) := by
  rw [fb_kb, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem kb_toNat {s : State} (hp : PreF X s) : (kb s).toNat + (frameBytes + 8) + 8 + 112 ≤ 2 ^ 64 ∧
    (kb s).toNat + (frameBytes + 8) = (s.gpr .rsp).toNat ∧ 8 ≤ (kb s).toNat := by
  have := hp.sp1; have := hp.sp2
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold stackBytes frameBytes at *; omega_arith

theorem toNat_off {p : Addr} {d : Nat} (h : p.toNat + d < 2 ^ 64) : (off p d).toNat = p.toNat + d := by
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

/-- The stack argument `i` of a function called from the frame is the
frame's word `8 i`. -/
theorem stackArg_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) {i : Nat} (hi : i < 400) :
    stackArg (t.callEntry.withRegions rd wr) i = word t.mem (fb s) (8 * i) := by
  have hsep := Offset.sep (kb s) (d := 8 * (i + 1)) (n := 8) (e := 0) (k := 8) (by omega_arith) (by omega_arith) (by omega_arith)
  rw [show kb s + BitVec.ofNat 64 0 = kb s from BitVec.add_zero _] at hsep
  simp only [stackArg, stackArgAddr, State.withRegions_mem, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_mem, hsp, fb_sub8]
  rw [Mem.readW_writeW_sep hsep (by decide)]
  show _ = t.mem.readW (off (fb s) (8 * i)) 64
  rw [fb_kb, ← off, off_off, show 8 + 8 * i = 8 * (i + 1) by omega_arith]

theorem stackArgAddr_entry {s t : State} (hsp : t.gpr .rsp = fb s) (rd wr : List Region) :
    stackArgAddr (t.callEntry.withRegions rd wr) 0 = fb s := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hsp, fb_sub8]
  rw [fb_kb]

/-- What the CRT writes: `M` and the working space. -/
def crtWr (s : State) : List Region :=
  [⟨off (fb s) oM, (s.gpr .rcx).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]

/-- The return address of the CRT's calls is in the stack the function
uses, below its own. -/
theorem hole_sub (s : State) : Region.Sub (hole (kb s)) (stkR s) := by
  rw [show hole (kb s) = ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, 8⟩ by
    simp only [hole, kb, BitVec.sub_sub]; rfl]
  exact Region.sub_prefix (by decide)

/-- Frame bytes at `d` are apart from the return address of the CRT's calls. -/
theorem frame_hole {s : State} (hp : PreF X s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Disjoint ⟨kb s + BitVec.ofNat 64 (8 + d), n⟩ (hole (kb s)) := by
  have ⟨hK1, _, _⟩ := kb_toNat hp
  exact Offset.disjoint_below (kb s) (n := 8) (by unfold frameBytes at h hK1; omega_arith)

/-! ## Memory across a call from the frame -/

/-- The return address a call from the frame stores. -/
theorem callEntry_frame {s t : State} (hsp : t.gpr .rsp = fb s) : Frame [below (fb s) 8] t.mem t.callEntry.mem := by
  rw [State.callEntry_mem, hsp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (below_call _ (by decide) (by decide))

/-- A buffer of the caller that the function does not write, from memory
changed only where it may write. -/
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

/-- The return address's bytes are in the stack the function uses. -/
theorem below_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := ret_sub s

/-- Memory changed by a call from the frame, within regions in the stack
the function uses, `out` or the working space. -/
theorem frame_call {s : State} {m₁ m₂ m₃ : Mem} (h₁ : Frame [stkR s, outR s, scrR s] m₁ m₂) {rs : List Region}
    (h₂ : Frame rs m₂ m₃) (hs : ∀ r ∈ rs, Region.Sub r (stkR s) ∨ Region.Sub r (outR s) ∨ Region.Sub r (scrR s)) :
    Frame [stkR s, outR s, scrR s] m₁ m₃ :=
  h₁.trans (h₂.sub fun r hr => by
    rcases hs r hr with h | h | h
    · exact ⟨_, List.mem_cons_self .., h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), h⟩)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

/-- A slot kept by a call that writes regions apart from it. -/
theorem slot_keep {s : State} {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, (⟨off (fb s) d, 8⟩ : Region).Disjoint r) : word m' (fb s) d = word m (fb s) d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-! ## The call -/

/-- The slots are apart from `M`, the working space and the return address. -/
theorem slot_apart {s : State} (hp : PreF X s) {d : Nat} (hd' : d + 8 ≤ oM) :
    ∀ r ∈ crtWr s ++ [below (fb s) 16], (⟨off (fb s) d, 8⟩ : Region).Disjoint r := by
  have e2 : oM = 168 := rfl
  have hk2 := hp.k2
  intro r hr
  simp only [crtWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact (hp.dKs.sub_left (frame_sub s (by unfold frameBytes; omega_arith)))
  · exact Offset.disjoint_below (fb s) (n := 16) (by omega_arith)

end VG.Proof.Rsa.X86_64

end

end

/-! ### `Rsa.X86_64.PrivPc`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precompute`

`r₁` kept in its slot, and `n`'s values written to the frame at `oPre`
(`pc_stage`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- A stack argument past a store to the frame. -/
theorem arg_wo {s : State} (m : Mem) {d : Nat} (v : BitVec 64) (hd : d + 8 ≤ frameBytes) {j : Nat} (hj : j < 14) :
    (m.writeW (off (fb s) d) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  rw [stackArgAddr_fb]
  exact word_wo m (fb s) v (by unfold frameBytes at *; omega_using [hd]) (by unfold frameBytes at *; omega_using [hd])
    (by unfold frameBytes; omega_using [hj])

/-- `2 ⌈k / 8⌉` from `k`. -/
theorem preWords_val {x : BitVec 64} (hx : x.toNat ≤ 1024) :
    (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 + (x + BitVec.signExtend 64 (7 : BitVec 32)) >>> 3 =
      BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  rw [sx7]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords, show (7 : BitVec 64).toNat = 7 from rfl]
  omega_using [hx]

/-! ## The call -/

theorem preWords_le {s : State} (hp : PreF X s) : Spec.Rsa.precomputedWords (s.gpr .rcx).toNat ≤ 256 := by
  have := hp.k2; unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_using [this]

/-- A region of the frame at `d`, apart from the return address of a call. -/
theorem ret_disjoint (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (below (fb s) 8).Disjoint ⟨off (fb s) d, n⟩ := by
  rw [show below (fb s) 8 = ⟨kb s, 8⟩ by simp only [below]; rw [← fb_sub8]; rfl, fb_off]
  exact Offset.base_disjoint _ (by omega_using []) (by unfold frameBytes at h; omega_using [h])

end VG.Proof.Rsa.X86_64

end

end


/-!
# `vg_rsa_private_checked` on x86-64: the call of `vg_rsa_public_precomputed_checked`

`r₃` kept in its slot, and `M^e mod n` written to `out` (`pd_stage`), for
whatever `M` holds.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem arg_in {s t : State} (hp : PreF X s) (he : Env s t) {j : Nat} (hj : j < 14) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 :=
  ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
    rw [he.rd, hp.hrd]; simp),
    by rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩

theorem word_wo0 (m : Mem) (base : Addr) (v : BitVec 64) {d' : Nat} (h : 8 ≤ d') (hd' : d' + 8 ≤ 4096) :
    (m.writeW base v).readW (off base d') 64 = m.readW (off base d') 64 := by
  have := word_wo m base v (d := 0) (d' := d') (.inl (by omega_arith)) (by decide) hd'
  simpa only [Bignum.word, off, BitVec.add_zero] using this

theorem arg_wo0 {s : State} (m : Mem) (v : BitVec 64) {j : Nat} (hj : j < 14) :
    (m.writeW (fb s) v).readW (stackArgAddr s j) 64 = m.readW (stackArgAddr s j) 64 := by
  have := arg_wo (s := s) m v (d := 0) (by decide) hj
  simpa only [off, BitVec.add_zero] using this

/-! ## The call -/

/-- `M` in the frame, `k` bytes. -/
def mR (s : State) : Region := ⟨off (fb s) oM, (s.gpr .rcx).toNat⟩

theorem mR_sub {s : State} (hp : PreF X s) : Region.Sub (mR s) (stkR s) :=
  frame_sub s (by have := hp.k2; unfold oM frameBytes; omega_arith)

/-- What it writes: `out` and the working space. -/
def pdWr (s : State) : List Region := [⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩, scrR s]

theorem word_self0 (m : Mem) (base : Addr) (v : BitVec 64) : word (m.writeW base v) base 0 = v := by
  have := word_writeW_self m base 0 v
  simpa only [off, BitVec.add_zero] using this

/-- Bytes of the frame at `d`, kept by a call's return address. -/
theorem entry_bytes {s t : State} (hsp : t.gpr .rsp = fb s) {d n : Nat} (h : d + n ≤ frameBytes) :
    Spec.Rsa.bytesAt t.callEntry.mem (off (fb s) d) n = Spec.Rsa.bytesAt t.mem (off (fb s) d) n := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => (callEntry_frame hsp).bytes (R := ⟨off (fb s) d, n⟩)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact (ret_disjoint s h).symm)
    (by dsimp only; unfold frameBytes at h; omega_arith) (List.mem_range.mp hi)

end VG.Proof.Rsa.X86_64

end

end

/-!
# `vg_rsa_private_checked` on x86-64: the check and the release

After the calls, `out` (which `vg_rsa_public_precomputed_checked` wrote) is
compared with the input without branches (`cmpLoop_ok`), and `M` is
released to `out` under the mask of `r₁ = r₂ = r₃ = 1` and their equality,
and zeroed (`releaseLoop_ok`), whatever `M` and `out` hold (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64

variable {X : List Region}

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.WriteBytes (writeW8_apply)

/-- The comparison's registers. -/
theorem cmpArgs_ok {s t : State} (hp : PreF X s) (he : Env s t) :
    WP isa (.block cmpArgs) t fun t' => t'.mem = t.mem ∧
      t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0 ∧ Keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] t t' := by
  obtain hs := he.scr hp
  refine WP.mono (WP.keep [.rax, .r11, .rdi, .rsi, .rcx, .r10, .rdx] (c := .block cmpArgs) (Q := fun t' =>
      t'.mem = t.mem ∧ t'.gpr .r11 = gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) ∧
      t'.gpr .rdi = s.gpr .rdi ∧ t'.gpr .rsi = stackArg s 0 ∧ t'.gpr .rcx = s.gpr .rcx ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ t'.gpr .rdx = 0) (by
    xrun [cmpArgs, gOf, ea_sp, he.rsp, arg, hs.ld (d := oR1) (by decide), hs.ld (d := oR3) (by decide),
      hs.ld (d := oOut) (by decide), hs.ld (d := oK) (by decide), arg_in hp he (show 0 < 14 by decide),
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fb s 0).symm,
      he.sOut, he.sK, he.arg hp (show 0 < 14 by decide)]) rfl) fun t' ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, k⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, k⟩

/-- After `j` bytes of the comparison. -/
structure CmpInv (t₀ : State) (op ip : Addr) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r9, .r10, .rdx] t₀ t
  mem : t.mem = t₀.mem
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  rdx : t.gpr .rdx = 0 ↔ ∀ i < j, t₀.mem (op + BitVec.ofNat 64 i) = t₀.mem (ip + BitVec.ofNat 64 i)

/-- The comparison of the `k` bytes at `op` and `ip`: `rdx` is zero exactly
when they are equal. -/
theorem cmpLoop_ok {t : State} {op ip : Addr} {k : Nat} (hk1 : 1 ≤ k) (hk : k < 2 ^ 63)
    (hdi : t.gpr .rdi = op) (hsi : t.gpr .rsi = ip) (hcx : t.gpr .rcx = BitVec.ofNat 64 k)
    (h10 : t.gpr .r10 = BitVec.ofNat 64 0) (hdx : t.gpr .rdx = 0)
    (ho : ∀ i < k, InRegions (t.rd ++ t.wr) (op + BitVec.ofNat 64 i) 1)
    (hi : ∀ i < k, InRegions (t.rd ++ t.wr) (ip + BitVec.ofNat 64 i) 1) :
    WP isa cmpLoop t fun t' => CmpInv t op ip k t' := by
  refine wp_upto (a := 0) (N := k) (by omega_arith) (CmpInv t op ip) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, rfl, h10, ⟨fun _ _ h => absurd h (by omega_arith), fun _ => hdx⟩⟩
  intro j _ hj u hI
  obtain hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  obtain hsi' : u.gpr .rsi = ip := (hI.keep.gpr (by decide)).trans hsi
  obtain hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  obtain hoj : InRegions (u.rd ++ u.wr) (op + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact ho j hj
  obtain hij : InRegions (u.rd ++ u.wr) (ip + BitVec.ofNat 64 j) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hi j hj
  refine WP.mono (WP.keep [.rax, .r9, .r10, .rdx] (Q := fun u' => u'.mem = u.mem ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k)) ∧
      u'.gpr .rdx = u.gpr .rdx ||| (BitVec.setWidth 64 (u.mem (op + BitVec.ofNat 64 j)) ^^^
        BitVec.setWidth 64 (u.mem (ip + BitVec.ofNat 64 j)))) (by
    xrun [cmpLoop, State.ea, at10, hdi', hsi', BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
      BitVec.add_zero, hoj, hij, hI.r10, hcx', ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show k < 2 ^ 64 by omega_arith)]) rfl) fun u' ⟨⟨hm, h10', hz, hdx'⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), hm.trans hI.mem, h10', ?_⟩
  rw [hdx', show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl,
    zext_xor_eq_zero, hI.rdx, hI.mem]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h1 i hi
    · exact h2
  · intro h
    exact ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩

theorem masks_ok {t : State} {g : BitVec 64} {eq : Bool} (h11 : t.gpr .r11 = g) (hg : g = 0 ∨ g = 1)
    (hdx : t.gpr .rdx = 0 ↔ eq = true) :
    WP isa (.block masks) t fun t' => t'.mem = t.mem ∧ t'.gpr .r9 = relMask g eq ∧ t'.gpr .r11 = result g eq ∧
      t'.gpr .r10 = BitVec.ofNat 64 0 ∧ Keep [.rdx, .r9, .rax, .r8, .r11, .r10] t t' := by
  obtain hcf : decide ((t.gpr .rdx).toNat < BitVec.toNat (1 : BitVec 64)) = eq := by
    rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]
    cases eq
    · have : t.gpr .rdx ≠ 0 := fun h => by simpa using hdx.mp h
      simp only [decide_eq_false_iff_not, Nat.lt_one_iff]
      intro h; exact this (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · simp only [decide_eq_true_eq, Nat.lt_one_iff, hdx.mpr rfl]; rfl
  refine WP.mono (WP.keep [.rdx, .r9, .rax, .r8, .r11, .r10] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .r9 = relMask g eq ∧ t'.gpr .r11 = result g eq ∧ t'.gpr .r10 = BitVec.ofNat 64 0) (by
    xrun [masks, h11, hcf]
    rcases hg with rfl | rfl <;> cases eq <;> decide) rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, k⟩

/-- After `j` bytes of the release. -/
structure RelInv (t₀ : State) (op Mb : Addr) (g : BitVec 64) (eq : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10] t₀ t
  r10 : t.gpr .r10 = BitVec.ofNat 64 j
  out : ∀ i < j, t.mem (op + BitVec.ofNat 64 i) = if g = 1 ∧ eq = true then t₀.mem (Mb + BitVec.ofNat 64 i) else 0
  m : ∀ i < j, t.mem (Mb + BitVec.ofNat 64 i) = 0
  frame : ∀ x, (∀ i < j, x ≠ op + BitVec.ofNat 64 i) → (∀ i < j, x ≠ Mb + BitVec.ofNat 64 i) → t.mem x = t₀.mem x

/-- The release: `out := M & mask`, `M := 0`, byte by byte. -/
theorem releaseLoop_ok {t : State} {S op : Addr} {k : Nat} {g : BitVec 64} {eq : Bool} (hk1 : 1 ≤ k)
    (hk : k < 2 ^ 63) (hsp : t.gpr .rsp = S) (hdi : t.gpr .rdi = op) (h9 : t.gpr .r9 = relMask g eq)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 k) (h10 : t.gpr .r10 = BitVec.ofNat 64 0)
    (hwo : ∀ i < k, InRegions t.wr (op + BitVec.ofNat 64 i) 1)
    (hwm : ∀ i < k, InRegions t.wr (off S oM + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < k, ∀ i' < k, op + BitVec.ofNat 64 i ≠ off S oM + BitVec.ofNat 64 i') :
    WP isa releaseLoop t fun t' => RelInv t op (off S oM) g eq k t' := by
  refine wp_upto (a := 0) (N := k) (by omega_arith) (RelInv t op (off S oM) g eq) ?_ (fun _ h => h)
    ⟨Keep.refl _ _, h10, fun _ h => absurd h (by omega_arith), fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl⟩
  intro j _ hj u hI
  obtain hsp' : u.gpr .rsp = S := (hI.keep.gpr (by decide)).trans hsp
  obtain hdi' : u.gpr .rdi = op := (hI.keep.gpr (by decide)).trans hdi
  obtain h9' : u.gpr .r9 = relMask g eq := (hI.keep.gpr (by decide)).trans h9
  obtain hcx' : u.gpr .rcx = BitVec.ofNat 64 k := (hI.keep.gpr (by decide)).trans hcx
  obtain hoj : InRegions u.wr (op + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwo j hj
  obtain hmj : InRegions u.wr (off S oM + BitVec.ofNat 64 j) 1 := by rw [hI.keep.2.2]; exact hwm j hj
  obtain hmj' : InRegions (u.rd ++ u.wr) (off S oM + BitVec.ofNat 64 j) 1 :=
    let ⟨r, hr, hc⟩ := hmj; ⟨r, List.mem_append_right _ hr, hc⟩
  obtain hb : u.mem (off S oM + BitVec.ofNat 64 j) = t.mem (off S oM + BitVec.ofNat 64 j) :=
    hI.frame _ (fun i hi h => hsep i (by omega_arith) j hj h.symm) fun i hi h => out_ne (by omega_arith) (by omega_arith)
      (show j ≠ i by omega_arith) h
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun u' =>
      u'.mem = (u.mem.writeW (op + BitVec.ofNat 64 j)
        (if g = 1 ∧ eq = true then t.mem (off S oM + BitVec.ofNat 64 j) else 0)).writeW
          (off S oM + BitVec.ofNat 64 j) (0 : Byte) ∧
      u'.gpr .r10 = BitVec.ofNat 64 (j + 1) ∧ u'.zf = some (decide (j + 1 = k))) (by
    xrun [releaseLoop, State.ea, at10, mByte, hsp', hdi', hI.r10, h9', hcx', BitVec.mul_one,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, BitVec.ofInt_natCast,
      show S + BitVec.ofNat 64 j + BitVec.ofNat 64 oM = off S oM + BitVec.ofNat 64 j by
        rw [off, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j)],
      hoj, hmj, hmj', hb, low_and_mask, ofNat_add_one,
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega_arith) (show k < 2 ^ 64 by omega_arith)]
    rfl) rfl) fun u' ⟨⟨hm, h10', hz⟩, k'⟩ => ⟨hz, (hI.keep.trans k').mono (by decide), h10', ?_, ?_, ?_⟩
  · intro i hi
    rw [hm, writeW8_apply, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega_arith) j hj)),
        ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_arith) (by omega_arith) (show i ≠ j by omega_arith)))]
      exact hI.out i hi
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (hsep i (by omega_arith) i (by omega_arith)))]; simp only [↓reduceIte]
  · intro i hi
    rw [hm, writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (out_ne (by omega_arith) (by omega_arith) (show i ≠ j by omega_arith))),
        writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false fun h => hsep j hj i (by omega_arith) h.symm)]
      exact hI.m i hi
    · simp only [↓reduceIte]
  · intro x hx hx'
    rw [hm, writeW8_apply, writeW8_apply, ite_eq_right_of_eq_false _ _ (eq_false (hx' j (by omega_arith))),
      ite_eq_right_of_eq_false _ _ (eq_false (hx j (by omega_arith)))]
    exact hI.frame x (fun i hi => hx i (by omega_arith)) fun i hi => hx' i (by omega_arith)

theorem contains_of_byte {r : Region} {p : Addr} {n : Nat} (h : r = ⟨p, n⟩) (hn : n ≤ 2 ^ 64) {i : Nat}
    (hi : i < n) : r.Contains (p + BitVec.ofNat 64 i) 1 := by
  subst h; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The check and the release, after the calls, from `t`: whatever `M`,
`out` and the values returned hold. -/
theorem tail_ok {s t : State} (hp : PreF X s) (he : Env s t) :
    WP isa (seqs PrivChecked.tail) t fun t' =>
      t'.gpr .rax = result (gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3))
        (decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat)) ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
        (if gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
            Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
              Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
          then Spec.Rsa.bytesAt t.mem (off (fb s) oM) (s.gpr .rcx).toNat
          else List.replicate (s.gpr .rcx).toNat 0) ∧
      Spec.Rsa.bytesAt t'.mem (off (fb s) oM) (s.gpr .rcx).toNat = List.replicate (s.gpr .rcx).toNat 0 ∧
      Env s t' := by
  have hk1 := hp.k1
  have hk2 := hp.k2
  have hsi := hp.hsi
  have hil := hp.hil
  -- The input, unchanged.
  obtain hin : Spec.Rsa.bytesAt t.mem (stackArg s 0) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat :=
    bytes_of_frame he.mem (by rw [← hil]; exact hp.dKi) (by rw [← hil]; exact hp.dOi) (by rw [← hil]; exact hp.dis.symm)
      (by omega_arith)
  obtain hout : (⟨s.gpr .rdi, (s.gpr .rcx).toNat⟩ : Region) ∈ t.wr := by
    rw [he.wr, hp.hwr, ← hsi]; simp
  obtain hinp : (⟨stackArg s 0, (s.gpr .rcx).toNat⟩ : Region) ∈ t.rd := by
    rw [he.rd, hp.hrd, ← hil]; simp
  obtain hfr : (⟨fb s, frameBytes⟩ : Region) ∈ t.wr := by rw [he.wr]; exact List.mem_cons_self ..
  obtain wO : (s.gpr .rcx).toNat ≤ 2 ^ 64 := by omega_arith
  unfold PrivChecked.tail
  simp only [seqs]
  refine WP.seq (WP.mono (cmpArgs_ok hp he) fun t₁ ⟨hm₁, h11, hdi, hsi₁, hcx, h10, hdx, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (k := (s.gpr .rcx).toNat) (op := s.gpr .rdi) (ip := stackArg s 0) (by omega_arith)
    (by omega_arith) hdi hsi₁ (by rw [hcx]; exact (ofNat_toNat _).symm) h10 hdx
    (fun i hi => ⟨_, List.mem_append_right _ (by rw [k₁.2.2]; exact hout), contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [k₁.2.1]; exact hinp), contains_of_byte rfl wO hi⟩))
    fun t₂ hI => ?_)
  obtain k12 := k₁.trans hI.keep
  obtain hrdx : t₂.gpr .rdx = 0 ↔ decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
      Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := by
    rw [hI.rdx, decide_eq_true_iff, ← hin, bytesAt_eq_iff, hm₁]
  refine WP.seq (WP.mono (masks_ok (h11 ▸ (hI.keep.gpr (by decide))) (gOf_cases _ _ _) hrdx)
    fun t₃ ⟨hm₃, h9, h11', h10', k₃⟩ => ?_)
  obtain k13 := k12.trans k₃
  obtain hsep : ∀ i < (s.gpr .rcx).toNat, ∀ i' < (s.gpr .rcx).toNat,
      s.gpr .rdi + BitVec.ofNat 64 i ≠ off (fb s) oM + BitVec.ofNat 64 i' := fun i hi i' hi' h => by
    obtain hc := contains_of_byte (r := mR s) rfl wO hi'
    rw [← h] at hc
    exact (hp.dKo.sub_left (mR_sub hp)) _ hc
      (contains_of_byte (r := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩) rfl (by omega_arith) (show i < (s.gpr .rsi).toNat by omega_arith))
  refine WP.seq (WP.mono (releaseLoop_ok (k := (s.gpr .rcx).toNat) (S := fb s) (by omega_arith) (by omega_arith)
    ((k13.gpr (by decide)).trans he.rsp) (((hI.keep.trans k₃).gpr (by decide)).trans hdi) h9 ?_ h10'
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hout, contains_of_byte rfl wO hi⟩)
    (fun i hi => ⟨_, by rw [k13.2.2]; exact hfr, by
      rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact Offset.contains_base _ (by unfold oM frameBytes; omega_arith) (by unfold oM; omega_arith)⟩)
    hsep) fun t₄ hR => ?_)
  · rw [((hI.keep.trans k₃).gpr (by decide)).trans hcx]; exact (ofNat_toNat _).symm
  obtain hm₃ : t₃.mem = t.mem := hm₃.trans (hI.mem.trans hm₁)
  obtain k14 := k13.trans hR.keep
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.gpr .rax = t₄.gpr .r11 ∧ t'.mem = t₄.mem) (by xrun) rfl)
    fun t' ⟨⟨hax, hm⟩, k'⟩ => ?_
  obtain k15 := k14.trans k'
  obtain hfr4 : Frame [outR s, mR s] t.mem t'.mem := fun x hx => by
    rw [hm, hR.frame x (fun i hi h => hx _ (List.mem_cons_self ..) (by
        rw [h]; exact contains_of_byte (r := outR s) rfl (by omega_arith) (show i < (s.gpr .rsi).toNat by omega_arith)))
      (fun i hi h => hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (by
        rw [h]; exact contains_of_byte rfl wO hi)), hm₃]
  obtain hslot : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ oM → word t'.mem (fb s) d = word t.mem (fb s) d := fun hd hd' =>
    slot_keep hfr4 fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.dKo.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_arith))
      · exact Offset.disjoint _ (.inl hd') (by unfold oM at hd'; omega_arith) (by unfold oM; omega_arith)
  refine ⟨hax.trans ((hR.keep.gpr (by decide)).trans h11'), ?_, ?_, ⟨(k15.gpr (by decide)).trans he.rsp,
    k15.2.1.trans he.rd, k15.2.2.trans he.wr, frame_call he.mem hfr4 fun r hr => ?_,
    (hslot (by decide) (by decide)).trans he.sOut, (hslot (by decide) (by decide)).trans he.sN,
    (hslot (by decide) (by decide)).trans he.sK, (hslot (by decide) (by decide)).trans he.sE,
    (hslot (by decide) (by decide)).trans he.sEl⟩⟩
  · by_cases hc : gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
          Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat
    · have hc' : gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true := ⟨hc.1, decide_eq_true hc.2⟩
      simp only [hc, and_self, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      exact List.map_congr_left fun i hi => by
        rw [hR.out i (List.mem_range.mp hi), hm₃]; simp only [hc', and_self, ↓reduceIte]
    · have hc' : ¬ (gOf (t.gpr .rax) (word t.mem (fb s) oR1) (word t.mem (fb s) oR3) = 1 ∧
          decide (Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rcx).toNat =
            Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rcx).toNat) = true) :=
        fun h => hc ⟨h.1, of_decide_eq_true h.2⟩
      simp only [hc, ↓reduceIte]
      simp only [Spec.Rsa.bytesAt, hm]
      refine List.ext_getElem (by simp) fun i h₁ _ => ?_
      simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [hR.out i (by simpa using h₁)]; simp only [hc', ↓reduceIte]
  · simp only [Spec.Rsa.bytesAt, hm]
    refine List.ext_getElem (by simp) fun i h₁ _ => ?_
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hR.m i (by simpa using h₁)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (sub_refl _))
    · exact .inl (mR_sub hp)

end VG.Proof.Rsa.X86_64
