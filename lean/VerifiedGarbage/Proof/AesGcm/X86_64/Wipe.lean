module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Short
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Gather
public import VerifiedGarbage.Proof.AesGcm.X86_64.Fast.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchOut
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratchWipeSlots
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.PowP
import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified

/-!
# AES-GCM on x86-64: `seal` and `open` with the keystream wiped

`seal` and `open` leave keystream in their working space, which is on the
stack: the last partial block's at `W + 80`, and, for some implementations,
more (the short path's, those of the blocks after the interleaved loops).
`sealSelW_framed` and `openSelW_framed` are `sealSel_framed` and
`openSel_framed` with slots `ss` of the working space zeroed after the code
(`withStackArgScratchSlots`); which slots each implementation needs is
for its registration to say. The contracts read memory on return only in
the buffers (`sealPost_out`, `openPost_out`), so the wipe keeps them.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.StackScratch.X86_64

/-- `sealCode_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealCodeW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.sealScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (withStackArgScratchSlots 2600 3 z ss c)
      (Spec.Gcm.sealContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.sealSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) z ss hss hv (by decide) (by decide) (by decide) hsp hxd (by decide)
    (sealPre_local _) (sealPost_local _) (sealPost_out _) sealFrameSat_pre

/-- `openCode_framed`, with the slots `ss` of the working space zeroed. -/
theorem openCodeW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) {c : Prog isa}
    (hv : Verified X86_64.target c (Proof.AesGcm.openScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (withStackArgScratchSlots 2608 4 z ss c)
      (Spec.Gcm.openContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.openSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) z ss hss hv
    (by decide) (by decide) (by decide) hsp hxd (by decide) (openPre_local _)
    (openPost_local _) (openPost_out _) openFrameSat_pre (hleak := openLeak_local _)

/-! ## The slots each implementation wipes

Found by scanning the stack after every function, for every implementation
and length: the GHASH accumulator at `W + 32` (which, with the tag, gives
`E(K, J₀)`) and the last partial block's keystream at `W + 80`, in `seal`,
`open` and `seal_split`; with AVX-512, the 64 bytes at `W + 1024` that the
end of a long `seal` writes (`Short.finKs`; the short path zeroes its
keystream `K` itself, `Short.kWipe`), the 8 bytes of keystream the
decryption of the bytes after the whole blocks leaves at `W + 1040` in
`open`, and 16 bytes of `seal_gather`'s; with `seal` ending without calls (`fin`), its keystream
(`W + 1024`, `W + 1040`; the eight-block loops zero the keystream of the
blocks after them themselves, `StitchAvx8.ksWipe`); and
with the other interleaved loops, the keystream of the blocks after them in
`open` and streaming decryption (`W + 768` to `W + 1088`). -/

/-- `StreamTo.framed_xdepth` for `withStackArgScratchSlots`. -/
theorem framedSlots_xdepth {bytes m d : Nat} {z : Zero} {ss : List Slot} {c : Prog isa}
    (h : c.x86_64Depth ≤ d) : (withStackArgScratchSlots bytes m z ss c).x86_64Depth ≤ d + bytes := by
  unfold withStackArgScratchSlots withStackArgScratchWipedSlots; split
  · exact StreamTo.framed_xdepth h
  · exact StreamTo.framed_xdepth (by simp only [Code.x86_64Depth, Nat.max_le]; exact ⟨h, Nat.zero_le _⟩)

/-- `StreamTo.framed_mx` for `withStackArgScratchSlots`. -/
theorem framedSlots_mx {bytes m : Nat} {z : Zero} {ss : List Slot} {c : Prog isa}
    (h : c.allInstrs (fun i => !loadsMxcsr i) = true) :
    (withStackArgScratchSlots bytes m z ss c).allInstrs (fun i => !loadsMxcsr i) = true := by
  unfold withStackArgScratchSlots withStackArgScratchWipedSlots; split
  · exact StreamTo.framed_mx h
  · refine StreamTo.framed_mx ?_
    rw [Code.allInstrs_eq] at h ⊢
    simp only [instrs, List.all_append, h, Bool.true_and, wipeSlots, List.all_cons, List.all_map]
    refine Bool.and_eq_true_iff.mpr ⟨by cases z <;> rfl, List.all_eq_true.mpr fun s _ => ?_⟩
    cases s <;> rfl

/-- 16-byte slots from byte `a` to `b` of the working space, with VEX's
`vmovdqu` if `avx`, else SSE2's `movdqu`. -/
def slots16 (avx : Bool) (a b : Nat) : List Slot :=
  (List.range ((b - a) / 16)).map fun k => if avx then .v16 (a + 16 * k) else .x (a + 16 * k)

theorem slots16_ok (avx : Bool) {a b : Nat} (h : b ≤ 2560) : ∀ s ∈ slots16 avx a b, s.disp + s.size ≤ 2560 := by
  intro s hs
  simp only [slots16, List.mem_map, List.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  cases avx <;> simp only [Bool.false_eq_true, ↓reduceIte, Slot.disp, Slot.size] <;> omega

/-- 32-byte slots from byte `a` to `b`, with VEX's `vmovdqu`. -/
def slots32 (a b : Nat) : List Slot := (List.range ((b - a) / 32)).map fun k => .v32 (a + 32 * k)

/-- 64-byte slots from byte `a` to `b`, with AVX-512's `vmovdqu32`. -/
def slots64 (a b : Nat) : List Slot := (List.range ((b - a) / 64)).map fun k => .z (a + 64 * k)

namespace GcmImpl

/-- Whether the implementation's code may use VEX. -/
def avx (v : GcmImpl) : Bool := v.features.contains "avx"

/-- How the wipes zero their register: in the code's own encoding. -/
def zero (v : GcmImpl) : Zero := if v.avx then .vex else .sse

/-- `seal`'s slots (and `seal_prepared`'s). -/
def sealSlots (v : GcmImpl) : List Slot :=
  slots16 v.avx 32 48 ++ slots16 v.avx 80 96 ++
    if v.short then slots64 1024 1088 else if v.fin then slots16 v.avx 1024 1056 else []

/-- `open`'s slots (and `open_prepared`'s). -/
def openSlots (v : GcmImpl) : List Slot :=
  slots16 v.avx 32 48 ++ slots16 v.avx 80 96 ++
    if v.short then slots16 v.avx 1040 1056 else if v.fin then []
    else if v.stitch.isSome then slots32 768 1088 else []

/-- `seal_split`'s slots. -/
def splitSlots (v : GcmImpl) : List Slot :=
  slots16 v.avx 32 48 ++ slots16 v.avx 80 96 ++ if v.fin then slots16 v.avx 1024 1056 else []

/-- `seal_gather`'s slots. -/
def gatherSlots (v : GcmImpl) : List Slot := if v.short then slots16 v.avx 168 184 else []

/-- `stream_encrypt`'s slots: none, since the eight-block loops zero their keystream. -/
def streamEncSlots (_v : GcmImpl) : List Slot := []

/-- `stream_decrypt`'s slots. -/
def streamDecSlots (v : GcmImpl) : List Slot :=
  if v.stitch.isSome && !v.short && !v.fin then slots32 768 1088 else []

end GcmImpl

theorem slots32_ok {a b : Nat} (h : b ≤ 2560) : ∀ s ∈ slots32 a b, s.disp + s.size ≤ 2560 := by
  intro s hs
  simp only [slots32, List.mem_map, List.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  simp only [Slot.disp, Slot.size]; omega

theorem slots64_ok {a b : Nat} (h : b ≤ 2560) : ∀ s ∈ slots64 a b, s.disp + s.size ≤ 2560 := by
  intro s hs
  simp only [slots64, List.mem_map, List.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  simp only [Slot.disp, Slot.size]; omega

theorem append_ok {xs ys : List Slot} {n : Nat} (hx : ∀ s ∈ xs, s.disp + s.size ≤ n)
    (hy : ∀ s ∈ ys, s.disp + s.size ≤ n) : ∀ s ∈ xs ++ ys, s.disp + s.size ≤ n := fun s hs => by
  rcases List.mem_append.mp hs with h | h
  · exact hx s h
  · exact hy s h

theorem nil_ok {n : Nat} : ∀ s ∈ ([] : List Slot), s.disp + s.size ≤ n := fun _ h => absurd h List.not_mem_nil

namespace GcmImpl

variable (v : GcmImpl)

theorem sealSlots_ok : ∀ s ∈ v.sealSlots, s.disp + s.size ≤ 2560 := by
  unfold sealSlots
  refine append_ok (append_ok (slots16_ok _ (by decide)) (slots16_ok _ (by decide))) ?_
  split
  · exact slots64_ok (by decide)
  · split
    · exact slots16_ok _ (by decide)
    · exact nil_ok

theorem openSlots_ok : ∀ s ∈ v.openSlots, s.disp + s.size ≤ 2560 := by
  unfold openSlots
  refine append_ok (append_ok (slots16_ok _ (by decide)) (slots16_ok _ (by decide))) ?_
  split
  · exact slots16_ok _ (by decide)
  · split
    · exact nil_ok
    · split
      · exact slots32_ok (by decide)
      · exact nil_ok

theorem splitSlots_ok : ∀ s ∈ v.splitSlots, s.disp + s.size ≤ 2560 := by
  unfold splitSlots
  refine append_ok (append_ok (slots16_ok _ (by decide)) (slots16_ok _ (by decide))) ?_
  split
  · exact slots16_ok _ (by decide)
  · exact nil_ok

theorem gatherSlots_ok : ∀ s ∈ v.gatherSlots, s.disp + s.size ≤ 184 := by
  unfold gatherSlots
  split
  · intro s hs
    simp only [slots16, List.mem_map, List.mem_range] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    split <;> simp only [Slot.disp, Slot.size] <;> omega
  · exact nil_ok

theorem streamEncSlots_ok : ∀ s ∈ v.streamEncSlots, s.disp + s.size ≤ 2560 := nil_ok

theorem streamDecSlots_ok : ∀ s ∈ v.streamDecSlots, s.disp + s.size ≤ 2560 := by
  unfold streamDecSlots
  split
  · exact slots32_ok (by decide)
  · exact nil_ok

end GcmImpl

variable (v : GcmImpl)

/-- `sealSel_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealSelW_framed (hF : Short.ShortFacts) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2600 3 z ss (v.sealCode v.callees))
      (Spec.Gcm.sealContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCode; split
  · exact sealCodeW_framed z ss hss
      (sealCode_verified (fun s hs => Short.sealM_correct v v.blkB hF s ⟨hs, trivial⟩)
        (ct_of_rel fun _ _ hp hp' hq => Short.sealM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.sealM_spSafe v v.blkB) (Short.sealM_xdepth v v.blkB)
  · split
    · exact sealCodeW_framed z ss hss
        (sealCode_verified (fun s hs => SealFin.sealFM_correct v v.blkB hF s ⟨hs, trivial⟩)
          (ct_of_rel fun _ _ hp hp' hq => SealFin.sealFM_rel v v.blkB hF ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
        (SealFin.sealFM_spSafe v v.blkB) (SealFin.sealFM_xdepth v v.blkB)
    · exact sealCodeW_framed z ss hss (seal_verified v) (seal_spSafe v) (seal_xdepth v)

/-- `openSel_framed`, with the slots `ss` of the working space zeroed. -/
theorem openSelW_framed (hF : Short.ShortFacts) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2608 4 z ss (v.openCode v.callees))
      (Spec.Gcm.openContract X86_64.abi 2632) := by
  unfold GcmImpl.openCode; split
  · exact openCodeW_framed z ss hss
      (openCode_verified (fun s hs => Short.openM_correct v v.blkB hF s ⟨hs, trivial⟩)
        (ct_of_rel fun _ _ hp hp' hq => Short.openM_rel hF v v.blkB ⟨hp, trivial⟩ ⟨hp', trivial⟩ hq))
      (Short.openM_spSafe v v.blkB) (Short.openM_xdepth v v.blkB)
  · exact openCodeW_framed z ss hss (open_verified v) (open_spSafe v) (open_xdepth v)

/-! ## With a prepared key context -/

section
variable (B : BlkFn Gcm.X86_64.Stitch.CtxMode.prepared)

theorem sealPreparedCodeW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560)
    {c : Prog isa} (hv : Verified X86_64.target c (Proof.AesGcm.sealPreparedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (withStackArgScratchSlots 2600 3 z ss c)
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.sealPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2600) z ss hss hv (by decide) (by decide) (by decide) hsp hxd (by decide)
    (Proof.AesGcm.sealPreparedPre_local _) (Proof.AesGcm.sealPrecomputedPost_local _)
    (Proof.AesGcm.sealPrecomputedPost_out _) sealFrameSatPrepared_pre

theorem openPreparedCodeW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560)
    {c : Prog isa} (hv : Verified X86_64.target c (Proof.AesGcm.openPreparedScratchContract X86_64.abi 24))
    (hsp : c.all (fun i => !X86_64.isa.writesSp i) = true) (hxd : c.x86_64Depth ≤ 24) :
    Verified X86_64.target (withStackArgScratchSlots 2608 4 z ss c)
      (Spec.Gcm.openPreparedContract X86_64.abi 2632) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.openPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.openPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.openPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (leak := some (Spec.Gcm.openLeak X86_64.abi.ptrBits)) (bytes := 2608) z ss hss hv
    (by decide) (by decide) (by decide) hsp hxd (by decide)
    (Proof.AesGcm.openPreparedPre_local _) (Proof.AesGcm.openPrecomputedPost_local _)
    (Proof.AesGcm.openPrecomputedPost_out _) openFrameSatPrepared_pre
    (hleak := Proof.AesGcm.openPrecomputedLeak_local _)

/-- `sealSelPrepared_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealSelPreparedW_framed (hF : Short.ShortFacts) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2600 3 z ss (v.sealCodeP (v.withBlk B)))
      (Spec.Gcm.sealPreparedContract X86_64.abi 2624) := by
  unfold GcmImpl.sealCodeP GcmImpl.sealCode; split
  · exact sealPreparedCodeW_framed z ss hss (sealPreparedCode_verified (Short.sealMP_correct v B hF)
      (Short.sealMW_ct hF v B Short.powOk_powersP Short.powersP_ct)) (Short.sealMP_spSafe v B)
      (Short.sealMP_xdepth v B)
  · split
    · exact sealPreparedCodeW_framed z ss hss (sealPreparedCode_verified (SealFin.sealFM_correct v B hF)
        (SealFin.sealFM_ct v B hF)) (SealFin.sealFM_spSafe v B) (SealFin.sealFM_xdepth v B)
    · exact sealPreparedCodeW_framed z ss hss (sealPrepared_verified v B) (sealM_spSafe v B) (sealM_xdepth v B)

/-- `openSelPrepared_framed`, with the slots `ss` of the working space zeroed. -/
theorem openSelPreparedW_framed (hF : Short.ShortFacts) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2608 4 z ss (v.openCodeP (v.withBlk B)))
      (Spec.Gcm.openPreparedContract X86_64.abi 2632) := by
  unfold GcmImpl.openCodeP GcmImpl.openCode; split
  · exact openPreparedCodeW_framed z ss hss (openPreparedCode_verified (Short.openMP_correct v B hF)
      (Short.openMW_ct hF v B Short.powOk_powersP Short.powersP_ct
        (FastOpen.openSel_rel hF v B (Short.longRel_openLong v B)))) (Short.openMP_spSafe v B)
      (Short.openMP_xdepth v B)
  · exact openPreparedCodeW_framed z ss hss (openPrepared_verified v B) (openM_spSafe v B) (openM_xdepth v B)

theorem streamEncryptPreparedW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2584 1 z ss (streamEncrypt (v.withBlk B)))
      (Spec.Gcm.streamEncryptPreparedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) z ss hss (streamEncryptPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamEncryptM_spSafe v B) (streamEncryptM_xdepth v B) (by decide) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamEncryptPrecomputedPost_local _) (Proof.AesGcm.streamEncryptPrecomputedPost_out _)
    streamEncryptFrameSatPrepared_pre

theorem streamDecryptPreparedW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2584 1 z ss (streamDecrypt (v.withBlk B)))
      (Spec.Gcm.streamDecryptPreparedContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.streamCryptPreparedSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamCryptPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) z ss hss (streamDecryptPrepared_verified v B) (by decide) (by decide) (by decide)
    (streamDecryptM_spSafe v B) (streamDecryptM_xdepth v B) (by decide) (Proof.AesGcm.streamCryptPreparedPre_local _)
    (Proof.AesGcm.streamDecryptPrecomputedPost_local _) (Proof.AesGcm.streamDecryptPrecomputedPost_out _)
    streamDecryptFrameSatPrepared_pre

end

/-! ## Streaming -/

theorem streamEncryptW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2584 1 z ss (streamEncrypt v.callees))
      (Spec.Gcm.streamEncryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamEncryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) z ss hss (streamEncrypt_verified v) (by decide) (by decide) (by decide)
    (streamEncrypt_spSafe v) (streamEncrypt_xdepth v) (by decide) (streamTextPre_local _)
    (streamEncryptPost_local _) (Proof.AesGcm.streamEncryptPost_out _) streamEncryptFrameSat_pre

theorem streamDecryptW_framed (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2584 1 z ss (streamDecrypt v.callees))
      (Spec.Gcm.streamDecryptContract X86_64.abi 2608) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.streamCryptSig) (nm := "scratch") (e := .u64)
    (n := 320) (pre := Spec.Gcm.streamTextPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.streamDecryptPost X86_64.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 2584) z ss hss (streamDecrypt_verified v) (by decide) (by decide) (by decide)
    (streamDecrypt_spSafe v) (streamDecrypt_xdepth v) (by decide) (streamTextPre_local _)
    (streamDecryptPost_local _) (Proof.AesGcm.streamDecryptPost_out _) streamDecryptFrameSat_pre

end VG.Proof.AesGcm.X86_64

namespace VG.Proof.AesGcm.X86_64.Split

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.StackScratch.X86_64
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Proof.AesGcm.X86_64.StreamTo (BlkToFn)
open VG.Proof.AesGcm.X86_64.Short (ShortFacts)

variable (v : GcmImpl)

/-- `sealSplit_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealSplitW_framed (hF : ShortFacts) (B : BlkFn CtxMode.base) (T : BlkToFn CtxMode.base) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target (withStackArgScratchSlots 2616 5 z ss (SealSplit.«seal» (v.splitMid (v.withBlk B) T.fn)))
      (Spec.Gcm.sealSplitContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.sealSplitSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealSplitPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) z ss hss (sealSplit_core v hF B T) (by decide) (by decide) (by decide)
    (sealSplit_spSafe v B T) (sealSplit_xdepth v B T) (by decide) (Proof.AesGcm.sealSplitPre_local _)
    (Proof.AesGcm.sealSplitPost_local _) (Proof.AesGcm.sealSplitPost_out _) splitFrameSat_pre

/-- `sealSplitPrepared_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealSplitPreparedW_framed (hF : ShortFacts) (B : BlkFn CtxMode.prepared) (T : BlkToFn CtxMode.prepared) (z : Zero)
    (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 2560) :
    Verified X86_64.target
      (withStackArgScratchSlots 2616 5 z ss (SealSplit.«seal» (v.splitMidR (v.withBlk B) T.fn)))
      (Spec.Gcm.sealSplitPreparedContract X86_64.abi 2672) :=
  X86_64.Verified.stackArgScratchSlots (sig := Spec.Gcm.sealSplitPreparedSig) (nm := "work") (e := .u64)
    (n := 320) (pre := Spec.Gcm.sealSplitPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealSplitPost X86_64.abi.ptrBits) (wa := true) (stack := 56)
    (bytes := 2616) z ss hss (sealSplitPrepared_core v B T hF) (by decide) (by decide) (by decide)
    (sealSplitR_spSafe v B T) (sealSplitR_xdepth v B T) (by decide) (Proof.AesGcm.sealSplitPreparedPre_local _)
    (Proof.AesGcm.sealSplitPrecomputedPost_local _) (Proof.AesGcm.sealSplitPrecomputedPost_out _)
    splitFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64.Split

namespace VG.Proof.AesGcm.X86_64.Gather

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.StackScratch.X86_64 VG.Impl.AesGcm.X86_64.SealGather
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- `sealGather_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealGatherW_framed (Sh : ShortFn CtxMode.base) (I : InitFn) (A : AadFn)
    (T : ToFn CtxMode.base) (F : FinFn) (z : Zero) (ss : List Slot) (hss : ∀ s ∈ ss, s.disp + s.size ≤ 184) :
    Verified X86_64.target
      (withStackArgScratchSlots 240 5 z ss (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchSlotsL (sig := Spec.Gcm.sealGatherSig) (nm := "scratch") (e := .u64) (n := 23)
    (pre := Spec.Gcm.sealGatherPre X86_64.abi.ptrBits) (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits)
    (wa := true) (stack := 4888) (bytes := 240) z ss hss (sealGather_core Sh I A T F) (by decide) (by decide)
    (by decide) (sealGather_spAll Sh I A T F) (sealGather_xdepth Sh I A T F) (by decide)
    (Proof.AesGcm.sealGatherPre_local _) (Proof.AesGcm.sealGatherPost_local _)
    (Proof.AesGcm.sealGatherPost_out _) gatherFrameSat_pre

/-- `sealGatherPrepared_framed`, with the slots `ss` of the working space zeroed. -/
theorem sealGatherPreparedW_framed (Sh : ShortFn CtxMode.prepared) (I : InitFn)
    (A : AadFn) (T : ToFn CtxMode.prepared) (F : FinFn) (z : Zero) (ss : List Slot)
    (hss : ∀ s ∈ ss, s.disp + s.size ≤ 184) :
    Verified X86_64.target
      (withStackArgScratchSlots 240 5 z ss (sealGather Sh.quick Sh.fast Sh.test Sh.code I.fn A.fn T.fn F.fn))
      (Spec.Gcm.sealGatherPreparedContract X86_64.abi 5128) :=
  X86_64.Verified.stackArgScratchSlotsL (sig := Spec.Gcm.sealGatherPreparedSig) (nm := "scratch") (e := .u64)
    (n := 23) (pre := Spec.Gcm.sealGatherPreparedPre X86_64.abi.ptrBits)
    (post := Spec.Gcm.sealGatherPost X86_64.abi.ptrBits) (wa := true) (stack := 4888) (bytes := 240) z ss hss
    (sealGatherPrepared_core Sh I A T F) (by decide) (by decide) (by decide) (sealGather_spAll Sh I A T F)
    (sealGather_xdepth Sh I A T F) (by decide) (Proof.AesGcm.sealGatherPreparedPre_local _)
    (Proof.AesGcm.sealGatherPrecomputedPost_local _) (Proof.AesGcm.sealGatherPrecomputedPost_out _)
    gatherFrameSatPrepared_pre

end VG.Proof.AesGcm.X86_64.Gather
