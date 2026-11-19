module

public import VerifiedGarbage.Proof.AesGcmSiv.X86.Keys
import VerifiedGarbage.Proof.AesGcmSiv.X86.TagIO
import VerifiedGarbage.Proof.AesGcmSiv.X86.Cmp
import VerifiedGarbage.Proof.AesGcmSiv.X86.Polyval
import VerifiedGarbage.Proof.AesGcm.X86.Absorb
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
public import VerifiedGarbage.Proof.GcmSiv.Words
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Spec.GcmSiv
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Run
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcmSiv.X86.Derive
public import VerifiedGarbage.Proof.Cmac.Block32
import VerifiedGarbage.Proof.AesGcm.X86.Cmp
import VerifiedGarbage.Proof.GcmSiv.Spec
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.GcmSiv.Ctr
import VerifiedGarbage.Proof.GcmSiv.Words32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Siv.Spec

/-! ### `AesGcmSiv.X86.Crypt`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.X86.Tag`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: a block encrypted with the encryption key (`tag`)

Untrusted: everything here is checked by Lean. `tag o` copies the block at
`W + 96` to `W + 112` (`copyMem`), zeroes the block at `W + o`, and calls
`vg_aes_ctr32_to` on that one block with the copy as the counter block: the
encryption of the block at `W + 96` with the encryption key's schedule at
`W + 512` (`tag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.X86 (at_ imm slot zero4)
open VG.Proof.AesGcm.X86 (w64 slotv slotv_eq GcmImpl readW_writeW_off zero4_fold)

theorem blockAt_zero4 (m : Mem) (p : Addr) : Spec.Gcm.blockAt (Proof.Cmac.zero4 m p) p = 0 := by
  rw [Spec.Gcm.blockAt, Proof.Cmac.zero4_bytes]
  decide

/-- The memory after the copy of the counter block. -/
def copyMem (m : Mem) (W : Addr) : Mem :=
  Proof.Cmac.store4 m (W + BitVec.ofNat 64 112) (m.readW (W + BitVec.ofNat 64 96) 32)
    (m.readW (W + BitVec.ofNat 64 100) 32) (m.readW (W + BitVec.ofNat 64 104) 32)
    (m.readW (W + BitVec.ofNat 64 108) 32)

theorem copyMem_frame (m : Mem) (W : Addr) : Frame [⟨W + BitVec.ofNat 64 112, 16⟩] m (copyMem m W) :=
  Proof.Cmac.frame_store4 _ _ _ _ _

theorem copyMem_bytes (m : Mem) (W : Addr) :
    bytesAt (copyMem m W) (W + BitVec.ofNat 64 112) 16 = bytesAt m (W + BitVec.ofNat 64 96) 16 := by
  rw [copyMem, Proof.Cmac.bytesAt_store4, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
    Proof.Cmac.le4_readW, Proof.Cmac.bytesAt_split4]
  simp only [add_ofNat_assoc, Nat.reduceAdd]

/-- The blocks a tag may be written to. -/
abbrev TagO (o : Nat) : Prop := o = 0 ∨ o = 224 ∨ o = 240

/-- What `tag o` writes. -/
abbrev tagWr (p : Prm) (o : Nat) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩,
    stk p]

theorem inMut_tagWr (p : Prm) {o : Nat} (ho : TagO o) : InMut p (tagWr p o) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · rcases ho with rfl | rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
    · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_stk p

/-- What `tag o` leaves, from `t`. -/
structure TagPost (p : Prm) (o : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = t.gpr .esi
  frame : Frame (tagWr p o) t.mem t'.mem
  out : bytesAt t'.mem (w64 p.W + BitVec.ofNat 64 o) 16 =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R (bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16)

/-- What `tag o`'s block leaves: the arguments of its call. -/
structure TagCall (p : Prm) (o : Nat) (t t₁ : State) : Prop where
  mem : t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)
  eax : t₁.gpr .eax = p.W + BitVec.ofNat 32 512
  ecx : t₁.gpr .ecx = BitVec.ofNat 32 p.R
  edx : t₁.gpr .edx = p.W + BitVec.ofNat 32 112
  ebx : t₁.gpr .ebx = p.W + BitVec.ofNat 32 o
  edi : t₁.gpr .edi = BitVec.ofNat 32 1
  esi : t₁.gpr .esi = t.gpr .esi
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem
  env : Env p t₁
  dst : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1)

/-- `tag o`'s block. -/
theorem tagArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : TagO o) :
    ∃ t₁, runBlock isa (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧ TagCall p o t t₁ := by
  have hw := L.ww
  obtain o₁ : o + 16 ≤ 2816 := by omega
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  obtain hz := zero4_fold (copyMem t.mem (w64 p.W)) p.W o
  obtain rR : (copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  obtain rR' : (Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o)).readW
      (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [← hz]
    rcases ho with rfl | rfl | rfl <;> simp (disch := decide) only [Nat.reduceAdd, readW_writeW_off] <;> exact rR
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ : ∃ t₁ : State, runBlock isa
      (copy16 cbO ccO ++ zero4 o ++ ctrArgs o) t = some t₁ ∧
      t₁.mem = Proof.Cmac.zero4 (copyMem t.mem (w64 p.W)) (w64 p.W + BitVec.ofNat 64 o) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.W + BitVec.ofNat 32 o ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    obtain hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
        (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) =
        copyMem t.mem (w64 p.W) := by
      simp only [copyMem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
    refine ⟨_, by simp only [copy16, zero4, ctrArgs]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, hz, rR'],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
      | (gregs [E.ebp, E.esp, rR']; done)
      | (gmems [hcp, hz]; done)
      | rfl
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 o, 16⟩] t.mem t₁.mem := by
    rw [hm₁, Proof.Cmac.zero4]
    exact ((copyMem_frame _ _).mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; simp)
  obtain E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact inMut_w p (.inl (by decide))
    · exact inMut_tagWr p ho _ (by simp))
  obtain hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.W + BitVec.ofNat 32 o) (16 * 1) :=
    dstW L E₁.perm (q := o) (by rcases ho with rfl | rfl | rfl <;> decide)
      (by rw [L.aW (by decide)]; exact Lay.w_w (.inr (by omega)) (by decide) (by omega_using [o₁]))
  exact ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩

theorem tag_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) {o : Nat} (ho : TagO o) :
    WP isa (tag v.callees o) t (TagPost p o t) := by
  have hw := L.ww
  obtain o₁ : o + 16 ≤ 2816 := by omega
  obtain ⟨t₁, run₁, ⟨hm₁, eax, ecx, edx, ebx, edi, si₁, rd₁, wr₁, f₁, E₁, hD⟩⟩ := tagArgs_ok L E ho
  obtain dO : (⟨w64 p.W + BitVec.ofNat 64 o, 16⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ :=
    Lay.w_w (by omega) (by omega_using [o₁]) (by decide)
  obtain hb₁ : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, Proof.Cmac.zero4, Proof.AesGcm.X86.bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact dO.symm) (by decide), copyMem_bytes]
  obtain hz₁ : Spec.Gcm.blockAt t₁.mem (w64 p.W + BitVec.ofNat 64 o) = 0 := by rw [hm₁]; exact blockAt_zero4 _ _
  obtain ek₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le)
      · exact (Lay.w_w (.inr (by omega)) (by decide) (by omega_using [o₁])).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_using [this])]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.mono (callCtr_ok v L E₁ (keyS L E₁.perm) hD
    (by rw [L.aW (by omega_using [o₁])]; exact inMut_tagWr p ho _ (by simp)) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  rw [L.aW (by omega_using [o₁])] at fc hout
  refine ⟨P.env, by rw [P.rd, rd₁], by rw [P.wr, wr₁], by rw [P.saved _ (by decide), si₁],
    (f₁.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> simp).trans (fc.mono fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp), ?_⟩
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    hz₁, Proof.Cmac.ctr32_one, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  rw [Proof.Cmac.bytesAt_blockAt, hout, Spec.Gcm.blockAt,
    Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
    show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
      Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, ek₁, hb₁]

end VG.Proof.AesGcmSiv.X86

end

end


/-!
# AES-GCM-SIV on x86: counter mode (`crypt`)

Untrusted: everything here is checked by Lean. The counter block at
`W + 96` starts as the tag with the top bit of its last byte set
(`cryptHead_ok`); each block of the data is encrypted in place by
`vg_aes_ctr32_to` from a copy of it at `W + 112`, after which its first word is
incremented (`cryptBlock_ok`); the last bytes are XORed with the keystream
block, computed at `W + 224` (`cryptTail_ok`). `crypt_ok`: the data becomes
`ctr` of it (RFC 8452 §4). The pointer is in `esi` and the number of bytes
left at `W + nO`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.WriteBytes (writeBytes)
open VG.Impl.AesGcm.X86 (at_ imm slot xorLoop)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add slotv slotv_eq GcmImpl readW_writeW_off covers_left
  covers_off XorPre XorPost xorLoop_ok xorBytes length_bytesAt sub_beq32)

theorem ctr32_single (ciph : Spec.Gcm.Block → Spec.Gcm.Block) (icb x : Spec.Gcm.Block) :
    Spec.Gcm.ctr32 ciph icb [x] = [x ^^^ ciph icb] := by
  simp [Spec.Gcm.ctr32, Spec.Gcm.keystream, Nat.repeat]

theorem toBytes_xor (a b : Spec.Gcm.Block) :
    Spec.Gcm.toBytes (a ^^^ b) = Spec.Cmac.xor (Spec.Gcm.toBytes a) (Spec.Gcm.toBytes b) := by
  apply List.ext_getElem (by simp [Spec.Gcm.toBytes, Spec.Cmac.xor])
  intro i h₁ h₂
  simp [Spec.Gcm.toBytes, Spec.Cmac.xor, BitVec.extractLsb'_xor]

/-- What the counter block at `W + 96` holds before block `j`: the first
word of `icb` plus `j`, and the rest of `icb`. -/
structure CtrSt (W : Addr) (icb : List Byte) (j : Nat) (m : Mem) : Prop where
  word : m.readW (W + BitVec.ofNat 64 96) 32 = BitVec.ofNat 32 (Spec.GcmSiv.leNat (icb.take 4) + j)
  rest : bytesAt m (W + BitVec.ofNat 64 100) 12 = icb.drop 4

theorem CtrSt.block {W : Addr} {icb : List Byte} {j : Nat} {m : Mem} (h : CtrSt W icb j m) :
    bytesAt m (W + BitVec.ofNat 64 96) 16 = Spec.GcmSiv.counterBlock icb j := by
  rw [GcmSiv.counterBlock_word, show (16 : Nat) = 4 + 12 from rfl, Proof.Cmac.bytesAt_add, ← Proof.Cmac.le4_readW,
    h.word, add_ofNat_assoc, h.rest]

/-- Bytes of a buffer outside the part a frame may also change. -/
theorem frame_outside {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr} {len a n : Nat}
    (hrs : ∀ r ∈ rs, r = ⟨P + BitVec.ofNat 64 a, n⟩ ∨ (⟨P, len⟩ : Region).Disjoint r) (hlen : len < 2 ^ 64)
    (han : a + n ≤ len) : ∀ p < len, (p < a ∨ a + n ≤ p) → m' (P + BitVec.ofNat 64 p) = m (P + BitVec.ofNat 64 p) :=
  fun p hp ho => hf _ fun r hr hc => by
    rcases hrs r hr with rfl | hd
    · exact Offset.disjoint P (d := p) (n := 1) (by omega_arith) (by omega_arith) (by omega_arith) _ (Region.contains_self _ _) hc
    · exact hd _ (Offset.contains_base P (show p + 1 ≤ len by omega_arith) (by omega_arith)) hc

/-- What counter mode writes: the counter block and its copy, the bytes
left, the block at `W + 224`, `vg_aes_ctr32_to`'s working space, the data and
the stack below `SP`. -/
abbrev cryR (p : Prm) : List Region :=
  [⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, ⟨w64 p.W + BitVec.ofNat 64 224, 16⟩,
    ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, ⟨w64 p.D, p.n⟩, stk p]

theorem inMut_cryR (p : Prm) : InMut p (cryR p) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact inMut_w p (.inl (by decide))
  · exact inMut_w p (.inr (.inl ⟨by decide, by decide⟩))
  · exact inMut_w p (.inr (.inr (.inl ⟨by decide, by decide⟩)))
  · exact inMut_w p (.inr (.inr (.inr ⟨by decide, by decide⟩)))
  · exact inMut_d p
  · exact inMut_stk p

/-- Byte `j` of the data, as a 64-bit address. -/
theorem Lay.dA {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : w64 (p.D + BitVec.ofNat 32 j) = w64 p.D + BitVec.ofNat 64 j :=
  w64_add (by have := L.dw; omega_arith)

theorem Lay.dN {p : Prm} (L : Lay p) {j : Nat} (hj : j < p.n) : (p.D + BitVec.ofNat 32 j).toNat = p.D.toNat + j :=
  toNat_add32 (by have := L.dw; omega_arith)

/-- What a block of counter mode leaves, from `t`. -/
structure BlockPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (j : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1))
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * (j + 1))
  z : t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0))
  ctr : CtrSt (w64 p.W) icb (j + 1) t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * (j + 1))
  frame : Frame (cryR p) t.mem t'.mem

/-- The arguments of a block's call. -/
theorem blkArgs_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat}
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) :
    ∃ t₁ : State, runBlock isa blockArgs t = some t₁ ∧ t₁.mem = copyMem t.mem (w64 p.W) ∧
      t₁.gpr .eax = p.W + BitVec.ofNat 32 512 ∧ t₁.gpr .ecx = BitVec.ofNat 32 p.R ∧
      t₁.gpr .edx = p.W + BitVec.ofNat 32 112 ∧ t₁.gpr .ebx = p.D + BitVec.ofNat 32 (16 * j) ∧
      t₁.gpr .edi = BitVec.ofNat 32 1 ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧ t₁.gpr .esi = t.gpr .esi ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hR := E.slots.rounds
  simp only [slotv_eq, roundsO] at hR
  obtain hcp : ((((t.mem.writeW (w64 p.W + BitVec.ofNat 64 112) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 116) (t.mem.readW (w64 p.W + BitVec.ofNat 64 100) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 120) (t.mem.readW (w64 p.W + BitVec.ofNat 64 104) 32)).writeW
      (w64 p.W + BitVec.ofNat 64 124) (t.mem.readW (w64 p.W + BitVec.ofNat 64 108) 32)) = copyMem t.mem (w64 p.W) := by
    simp only [copyMem, Proof.Cmac.store4, add_ofNat_assoc, Nat.reduceAdd]
  obtain rR : (copyMem t.mem (w64 p.W)).readW (w64 p.W + BitVec.ofNat 64 148) 32 = BitVec.ofNat 32 p.R := by
    rw [copyMem, Proof.Cmac.store4]
    simp (disch := decide) only [add_ofNat_assoc, Nat.reduceAdd, readW_writeW_off]
    exact hR
  refine ⟨_, by simp only [blockArgs, copy16]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, hcp, rR], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · gmems [hcp]
  · gregs [E.ebp]
  · gregs [rR]
  · gregs [E.ebp]
  · gregs [hsi]
  · gregs []
  · gregs [E.ebp]
  · gregs [E.esp]
  · gregs []
  all_goals rfl

/-- The code after a block's call. -/
theorem blkPost_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) {j : Nat} (hj : 16 * (j + 1) ≤ p.n)
    (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j)) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) :
    ∃ t' : State, runBlock isa blockNext t = some t' ∧
      t'.mem = (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 + BitVec.ofNat 32 1)).writeW (w64 p.W + BitVec.ofNat 64 176)
        (BitVec.ofNat 32 (p.n - 16 * (j + 1))) ∧
      t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * (j + 1)) ∧
      t'.zf = some (decide ((p.n - 16 * (j + 1)) / 16 = 0)) ∧ t'.gpr .ebp = p.W ∧ t'.gpr .esp = p.SP ∧
      t'.rd = t.rd ∧ t'.wr = t.wr := by
  have hn' := L.n32
  simp only [slotv_eq, nO] at hn
  obtain e5 : BitVec.ofNat 32 (p.n - 16 * j) - BitVec.ofNat 32 16 = BitVec.ofNat 32 (p.n - 16 * (j + 1)) := by
    rw [ofNat_sub32 (by omega_arith) (by omega_arith), show p.n - 16 * j - 16 = p.n - 16 * (j + 1) by omega_arith]
  obtain rn : (t.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
      BitVec.ofNat 32 1)).readW (w64 p.W + BitVec.ofNat 64 176) 32 = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), hn]
  refine ⟨_, by simp only [blockNext, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR, rn, e5], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [rn, e5]
  · gregs [hsi, add32_ofNat_assoc, Nat.mul_succ]
  · gmems [rn, e5, ofNat_lsr32 (show p.n - 16 * (j + 1) < 2 ^ 32 by omega_arith)]
    rw [BitVec.and_self, show BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) =
      BitVec.ofNat 32 ((p.n - 16 * (j + 1)) / 16) - BitVec.ofNat 32 0 by simp, sub_beq32 (by omega_arith) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

theorem cryptBlock_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {j : Nat}
    (hj : 16 * (j + 1) ≤ p.n) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * j))
    (hn : slotv t.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j)) (C : CtrSt (w64 p.W) icb j t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptBlock v.callees) t (BlockPost p ciph icb x j t) := by
  have hw := L.ww
  have hn' := L.n32
  have hdw := L.dw
  obtain ⟨t₁, run₁, hm₁, eax, ecx, edx, ebx, edi, bp₁, sp₁, si₁, rd₁, wr₁⟩ := blkArgs_ok L E hsi
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩] t.mem t₁.mem := by rw [hm₁]; exact copyMem_frame _ _
  obtain E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut f₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq; exact inMut_w p (.inl (by decide)))
  obtain eQ : w64 (p.D + BitVec.ofNat 32 (16 * j)) = w64 p.D + BitVec.ofNat 64 (16 * j) := L.dA (by omega_arith)
  obtain dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  obtain hD : Dst p t₁ (p.W + BitVec.ofNat 32 512) (p.D + BitVec.ofNat 32 (16 * j)) (16 * 1) := by
    refine ⟨?_, by rw [L.dN (by omega_arith)]; omega_arith, ?_, ?_, ?_, ?_⟩ <;> rw [eQ]
    · exact covers_off E₁.perm.d (by omega_arith) (by omega_arith)
    · rw [L.aW (by decide)]; exact (dQ.sub_right (Lay.wSub (show 512 + 240 ≤ 2816 by decide))).symm
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact dQ.sub_right (Lay.wSub (by decide))
    · exact L.bd.sub_right (Offset.sub_base _ (by omega_arith))
  -- What the copy changed.
  obtain dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region)], (⟨w64 p.D, p.n⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.d_w' (by decide)
  obtain hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 112) 16 = Spec.GcmSiv.counterBlock icb j := by
    rw [hm₁, copyMem_bytes, C.block]
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [← hc]; unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain hx₁ : bytesAt t₁.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j) := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega_arith), hx]
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, WP.seq ?_⟩)
  refine WP.mono (callCtr_ok v L E₁ (keyS L E₁.perm) hD (by rw [eQ]; exact ⟨⟨w64 p.D, p.n⟩, by simp,
    Offset.sub_base _ (by omega_arith)⟩) eax ecx edx ebx edi) fun t₂ P => ?_
  have fc := P.frame
  have hout := P.out
  simp only [eQ, Nat.mul_one] at fc hout
  simp only [Spec.Gcm.blocksAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
    ctr32_single, List.cons.injEq, and_true] at hout
  rw [L.aW (by decide)] at hout
  obtain hb₂ : bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16 =
      Spec.Cmac.xor (bytesAt t₁.mem (w64 p.D + BitVec.ofNat 64 (16 * j)) 16) (GcmSiv.ksBlock ciph icb j) := by
    rw [Proof.Cmac.bytesAt_blockAt, hout, toBytes_xor, ← Proof.Cmac.bytesAt_blockAt, Spec.Gcm.blockAt,
      Proof.Cmac.aesWith_bytes _ _ (Proof.Cmac.bytesAt_length _ _ _), ← GcmSiv.aesWith_eq,
      show Spec.GcmSiv.aesWith p.R (bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 512) (16 * (p.R + 1))) =
        Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R from rfl, hc₁, hcb]
  obtain hk : (GcmSiv.ksBlock ciph icb j).length = 16 := by
    rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  obtain hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * j + 16) := by
    rw [← hxl] at hx₁ ⊢
    refine GcmSiv.ctrPart_step ciph icb x _ (by decide) hk hx₁ ?_ (by rw [hb₂, List.take_of_length_le (by omega_arith)])
    rw [hxl]
    refine frame_outside fc (fun q hq => ?_) (by omega_arith) (by omega_arith)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inl rfl
    · exact .inr (L.d_w' (by decide))
    · exact .inr L.bd.symm
  -- What the first two pieces changed.
  obtain f₂' : Frame [⟨w64 p.W + BitVec.ofNat 64 112, 16⟩, ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
      ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p] t.mem t₂.mem :=
    (f₁.mono fun q hq => by simp only [List.mem_singleton] at hq; subst hq; simp).trans fc
  obtain dC : ∀ {d k : Nat}, (96 ≤ d ∧ d + k ≤ 112 ∨ 176 ≤ d ∧ d + k ≤ 184) →
      ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 112, 16⟩ : Region), ⟨w64 p.D + BitVec.ofNat 64 (16 * j), 16⟩,
        ⟨w64 p.W + BitVec.ofNat 64 768, 2048⟩, stk p], (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint q :=
    fun h q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
      · exact (dQ.sub_right (Lay.wSub (by omega_arith))).symm
      · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
      · exact (L.bw' (by omega_arith)).symm
  obtain w₂ : t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 = t.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 :=
    f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inl ⟨Nat.le_refl _, by decide⟩)) (by decide)
  obtain n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * j) := by
    rw [← hn]; exact f₂'.readW (Region.contains_self _ _) (dC (k := 4) (.inr ⟨Nat.le_refl _, by decide⟩)) (by decide)
  obtain r₂ : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 100) 12 = bytesAt t.mem (w64 p.W + BitVec.ofNat 64 100) 12 :=
    Proof.AesGcm.X86.bytesAt_frame f₂' (dC (.inl ⟨by decide, by decide⟩)) (by decide)
  obtain si₂ : t₂.gpr .esi = p.D + BitVec.ofNat 32 (16 * j) := by rw [P.saved _ (by decide), si₁, hsi]
  obtain ⟨t₃, run₃, hm₃, si₃, z₃, bp₃, sp₃, rd₃, wr₃⟩ := blkPost_ok L P.env hj si₂ n₂
  obtain f₃ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem t₃.mem := by
    rw [hm₃]
    obtain g : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 4⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t₂.mem
        (t₂.mem.writeW (w64 p.W + BitVec.ofNat 64 96) (t₂.mem.readW (w64 p.W + BitVec.ofNat 64 96) 32 +
          BitVec.ofNat 32 1)) := (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
    exact g.writeW (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  obtain fm₃ : Frame (cryR p) t₂.mem t₃.mem := f₃.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain E₃ : Env p t₃ := P.env.mut L bp₃ sp₃ rd₃ wr₃ (frame_toMut fm₃ (inMut_cryR p))
  obtain f₂ : Frame (cryR p) t.mem t₂.mem := f₂'.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  refine WP.of_runBlock ⟨t₃, run₃, E₃, by rw [rd₃, P.rd, rd₁], by rw [wr₃, P.wr, wr₁], si₃,
    by rw [slotv_eq, hm₃, Mem.readW_writeW_self32], z₃, ⟨?_, ?_⟩, ?_, f₂.trans fm₃⟩
  · rw [hm₃, readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, w₂, C.word]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_arith
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide), r₂, C.rest]
  · rw [Proof.AesGcm.X86.bytesAt_frame f₃ (fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact L.d_w' (by decide)) (Nat.le_of_lt (by omega_arith)), hx₂,
      show 16 * j + 16 = 16 * (j + 1) by omega_arith]

/-- The encryption key's schedule misses what counter mode writes. -/
theorem key_cryR {p : Prm} (L : Lay p) :
    ∀ r ∈ cryR p, (⟨w64 p.W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.d_w' (by decide)).symm
  · exact (L.bw' (by decide)).symm

theorem ciph_cryR {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (cryR p) m m') :
    Spec.GcmSiv.ctxCiph m' (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph m (w64 p.W + BitVec.ofNat 64 512) p.R := by
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (key_cryR L r hr).sub_left (Region.sub_prefix L.rounds_le))
    (by have := L.rounds_le; omega_arith)]

/-- What the whole blocks of counter mode leave, from `t`. -/
structure BlocksPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (b : Nat) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  esi : t'.gpr .esi = p.D + BitVec.ofNat 32 (16 * b)
  n : slotv t'.mem p.W nO = BitVec.ofNat 32 (p.n - 16 * b)
  ctr : CtrSt (w64 p.W) icb b t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b)
  frame : Frame (cryR p) t.mem t'.mem

theorem blocks_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) (hb1 : 1 ≤ p.n / 16)
    (hsi : t.gpr .esi = p.D) (hn : slotv t.mem p.W nO = BitVec.ofNat 32 p.n)
    (C : CtrSt (w64 p.W) icb 0 t.mem) (hx : bytesAt t.mem (w64 p.D) p.n = x)
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (.loop (cryptBlock v.callees) .ne) t (BlocksPost p ciph icb x (p.n / 16) t) := by
  refine WP.loop (M := isa) (body := cryptBlock v.callees) (c := .ne)
    (fun (k : Nat) (t' : State) => ∃ j, k = p.n / 16 - j ∧ j < p.n / 16 ∧ BlocksPost p ciph icb x j t t') ?_
    (p.n / 16 - 0) t
    ⟨0, rfl, hb1, ⟨E, rfl, rfl, by rw [hsi, Nat.mul_zero, BitVec.add_zero], by rw [hn, Nat.mul_zero, Nat.sub_zero],
      C, by rw [hx, Nat.mul_zero, GcmSiv.ctrPart_zero], Frame.refl _ _⟩⟩
  rintro k t' ⟨j, rfl, hj, P⟩
  obtain hc' : Spec.GcmSiv.ctxCiph t'.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph := by
    rw [ciph_cryR L P.frame, hc]
  refine WP.mono (cryptBlock_ok v L P.env hxl (j := j) (by omega_arith) P.esi P.n P.ctr P.data hc') fun t'' Q => ?_
  obtain P' : BlocksPost p ciph icb x (j + 1) t t'' :=
    ⟨Q.env, Q.rd.trans P.rd, Q.wr.trans P.wr, Q.esi, Q.n, Q.ctr, Q.data, P.frame.trans Q.frame⟩
  obtain ev := eval_ne Q.z
  by_cases he : j + 1 = p.n / 16
  · left
    exact ⟨ev.trans (by simp; omega_arith), he ▸ P'⟩
  · right
    exact ⟨ev.trans (by simp; omega_arith), p.n / 16 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, P'⟩

/-- What the last bytes of counter mode leave, from `t`. -/
structure TailPost (p : Prm) (ciph : Spec.GcmSiv.Cipher) (icb x : List Byte) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  data : bytesAt t'.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x p.n
  frame : Frame (cryR p) t.mem t'.mem

theorem cryptTail_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t)
    {ciph : Spec.GcmSiv.Cipher} {icb x : List Byte} (hxl : x.length = p.n) {b r : Nat}
    (hn : p.n = 16 * b + r) (hr1 : 1 ≤ r) (hr : r < 16) (hsi : t.gpr .esi = p.D + BitVec.ofNat 32 (16 * b))
    (hnr : slotv t.mem p.W nO = BitVec.ofNat 32 r) (C : CtrSt (w64 p.W) icb b t.mem)
    (hx : bytesAt t.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b))
    (hc : Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R = ciph) :
    WP isa (cryptTail v.callees) t (TailPost p ciph icb x t) := by
  have hn' := L.n32
  have hdw := L.dw
  have hw := L.ww
  refine WP.seq (WP.mono (tag_ok v L E (o := 224) (by decide)) fun t₂ T => ?_)
  have fT := T.frame
  obtain dT : ∀ q ∈ tagWr p 224, (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain hx₂ : bytesAt t₂.mem (w64 p.D) p.n = GcmSiv.ctrPart ciph icb x (16 * b) := by
    rw [Proof.AesGcm.X86.bytesAt_frame fT dT (by omega_arith), hx]
  obtain hks : bytesAt t₂.mem (w64 p.W + BitVec.ofNat 64 224) 16 = GcmSiv.ksBlock ciph icb b := by
    rw [T.out, hc, C.block]
  obtain hnr₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 r := by
    rw [← hnr]
    exact fT.readW (Region.contains_self _ _) (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.bw' (by decide)).symm) (by decide)
  simp only [slotv_eq, nO] at hnr₂
  obtain ⟨t₃, run₃, dx₃, di₃, cx₃, m₃, bp₃, sp₃, rd₃, wr₃⟩ : ∃ t₃ : State, runBlock isa
      [.mov .edx (.reg .ebp), .alu .add .edx (imm bO), .mov .edi (.reg .esi), .mov .ecx (slot nO)] t₂ = some t₃ ∧
      t₃.gpr .edx = p.W + BitVec.ofNat 32 224 ∧ t₃.gpr .edi = p.D + BitVec.ofNat 32 (16 * b) ∧
      t₃.gpr .ecx = BitVec.ofNat 32 r ∧ t₃.mem = t₂.mem ∧ t₃.gpr .ebp = p.W ∧ t₃.gpr .esp = p.SP ∧ t₃.rd = t₂.rd ∧
      t₃.wr = t₂.wr :=
    ⟨_, by grun [T.env.ebp, L.aW, T.env.perm.wR, hnr₂], by gregs [T.env.ebp], by gregs [T.esi, hsi],
      by gregs [hnr₂], by gmems [], by gregs [T.env.ebp], by gregs [T.env.esp], by gmems [], by gmems []⟩
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  obtain eD := L.dA (j := 16 * b) (by omega_arith)
  obtain dQ : (⟨w64 p.D + BitVec.ofNat 64 (16 * b), r⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ :=
    L.d_w.sub_left (Offset.sub_base _ (by omega_arith))
  obtain lp : XorPre t₃ (p.W + BitVec.ofNat 32 224) (p.D + BitVec.ofNat 32 (16 * b)) r := by
    refine ⟨dx₃, di₃, cx₃, by omega_arith, by omega_arith, by rw [L.nW (by decide)]; omega_arith, by rw [L.dN (by omega_arith)]; omega_arith,
      ?_, ?_, ?_⟩
    · rw [rd₃, wr₃, L.aW (by decide)]
      exact covers_prefix (T.env.perm.wCR (show 224 + 16 ≤ 2816 by decide)) (by omega_arith)
    · rw [wr₃, eD]; exact covers_off T.env.perm.d (by omega_arith) (by omega_arith)
    · rw [eD, L.aW (by decide)]
      exact ((dQ.sub_right (Lay.wSub (show 224 + 16 ≤ 2816 by decide))).sub_right (Region.sub_prefix (by omega_arith))).symm
  refine WP.mono (xorLoop_ok t₃ lp) fun t₄ O => ?_
  have hm₄ := O.mem
  rw [m₃, eD, L.aW (by decide)] at hm₄
  obtain hl : (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r).length = r := by
    simp [xorBytes, Proof.Cmac.bytesAt_length]
  obtain fw := Proof.AesGcm.X86.writeBytes_frame' t₂.mem (q := w64 p.D + BitVec.ofNat 64 (16 * b)) hl
  rw [← hm₄] at fw
  obtain hk : (GcmSiv.ksBlock ciph icb b).length = 16 := by rw [← hc]; exact GcmSiv.ctxCiph_length _ _ _ _
  obtain fwm : Frame (mutR p) t₃.mem t₄.mem := by
    rw [m₃]
    exact frame_toMut fw fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩
  obtain E₄ : Env p t₄ := T.env.mut L
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), bp₃])
    (by rw [O.other _ (by decide) (by decide) (by decide) (by decide) (by decide), sp₃])
    (by rw [O.rd, rd₃]) (by rw [O.wr, wr₃]) (by rw [← m₃]; exact fwm)
  refine ⟨E₄, by rw [O.rd, rd₃, T.rd], by rw [O.wr, wr₃, T.wr], ?_, ?_⟩
  · have hb' : bytesAt t₄.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r = Spec.Cmac.xor
        (bytesAt t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) r) ((GcmSiv.ksBlock ciph icb b).take r) := by
      obtain e := Proof.AesGcm.X86.bytesAt_writeBytes_self t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b))
        (xorBytes t₂.mem (w64 p.D + BitVec.ofNat 64 (16 * b)) (w64 p.W + BitVec.ofNat 64 224) r) (by omega_arith)
      rw [hl] at e
      obtain hs := Proof.Cmac.bytesAt_add t₂.mem (w64 p.W + BitVec.ofNat 64 224) r (16 - r)
      rw [show r + (16 - r) = 16 by omega_arith, hks] at hs
      rw [hm₄, e, xorBytes, hs, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
      rfl
    have := GcmSiv.ctrPart_step ciph icb x _ (i := b) (n := r) (by omega_arith) hk (by rw [hxl]; exact hx₂)
      (frame_outside fw (fun q hq => by simp only [List.mem_singleton] at hq; exact .inl hq)
        (by rw [hxl]; omega_arith) (by omega_arith)) hb'
    rwa [hxl, ← hn] at this
  · refine (fT.sub fun q hq => ?_).trans (fw.sub fun q hq => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hq; subst hq
      exact ⟨⟨w64 p.D, p.n⟩, by simp, Offset.sub_base _ (by omega_arith)⟩

/-- What `crypt` leaves, from `t`. -/
structure CryptPost (p : Prm) (t t' : State) : Prop where
  env : Env p t'
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  frame : Frame (cryR p) t.mem t'.mem
  data : bytesAt t'.mem (w64 p.D) p.n =
    Spec.GcmSiv.ctr (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
      (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n)

/-- The memory `cryptHead` leaves: the counter block from the tag, and the
data's length as the bytes left. -/
def headMem (m : Mem) (W : Addr) (n : Nat) : Mem :=
  (Proof.Cmac.store4 m (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 32)
    (m.readW (W + BitVec.ofNat 64 4) 32) (m.readW (W + BitVec.ofNat 64 8) 32)
    (m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)).writeW (W + BitVec.ofNat 64 176) (BitVec.ofNat 32 n)

/-- The start of `crypt`: the counter block from the tag, and the data as
the bytes to encrypt. -/
theorem cryptHead_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁ : State, runBlock isa cryptHead t = some t₁ ∧ t₁.mem = headMem t.mem (w64 p.W) p.n ∧
      t₁.gpr .esi = p.D ∧ t₁.zf = some (decide (p.n / 16 = 0)) ∧ t₁.gpr .ebp = p.W ∧ t₁.gpr .esp = p.SP ∧
      t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  have hD := E.slots.data
  have hn := E.slots.len
  simp only [slotv_eq, dataO, lenO] at hD hn
  refine ⟨_, by simp only [cryptHead, onStr, wholeLeft]; grun [E.ebp, L.aW, E.perm.wW, E.perm.wR], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · gmems [headMem, Proof.Cmac.store4, add_ofNat_assoc, hD, hn]
  · gmems [hD, Proof.Cmac.store4, add_ofNat_assoc]
  · gmems [hD, hn, ofNat_lsr32 L.n32, Proof.Cmac.store4, add_ofNat_assoc]
    rw [BitVec.and_self, show BitVec.ofNat 32 (p.n / 16) = BitVec.ofNat 32 (p.n / 16) - BitVec.ofNat 32 0 by simp,
      sub_beq32 (by have := L.n32; omega_arith) (by decide)]
  · gregs [E.ebp]
  · gregs [E.esp]
  all_goals rfl

/-- What `cryptHead` leaves, from `t`. -/
structure CStart (p : Prm) (t t₁ : State) : Prop where
  env : Env p t₁
  rd : t₁.rd = t.rd
  wr : t₁.wr = t.wr
  esi : t₁.gpr .esi = p.D
  z : t₁.zf = some (decide (p.n / 16 = 0))
  n : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n
  ctr : CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem
  data : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n
  ciph : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
    Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R
  frame : Frame (cryR p) t.mem t₁.mem

theorem cryptStart_ok {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    ∃ t₁, runBlock isa cryptHead t = some t₁ ∧ CStart p t t₁ := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, hm₁, si₁, z₁, bp₁, sp₁, rd₁, wr₁⟩ := cryptHead_ok L E
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  obtain hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  obtain f₁ : Frame [⟨w64 p.W + BitVec.ofNat 64 96, 16⟩, ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩] t.mem t₁.mem := by
    rw [hm₁, headMem]
    exact ((Proof.Cmac.frame_store4 _ _ _ _ _).mono fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact List.mem_cons_self).writeW
      (List.mem_cons_of_mem _ List.mem_cons_self) _ (Region.contains_self _ _)
  obtain dD : ∀ q ∈ [(⟨w64 p.W + BitVec.ofNat 64 96, 16⟩ : Region), ⟨w64 p.W + BitVec.ofNat 64 176, 4⟩],
      (⟨w64 p.D, p.n⟩ : Region).Disjoint q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact L.d_w' (by decide)
  obtain hx₁ : bytesAt t₁.mem (w64 p.D) p.n = bytesAt t.mem (w64 p.D) p.n :=
    Proof.AesGcm.X86.bytesAt_frame f₁ dD (by omega_arith)
  obtain hc₁ : Spec.GcmSiv.ctxCiph t₁.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
      Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame f₁ (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        exact (Lay.w_w (.inr (by decide)) (by decide) (by decide)).sub_left (Region.sub_prefix L.rounds_le))
      (by have := L.rounds_le; omega_arith)]
  obtain hcb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      bytesAt (Proof.Cmac.store4 t.mem (w64 p.W + BitVec.ofNat 64 96) (t.mem.readW (w64 p.W + BitVec.ofNat 64 0) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 4) 32) (t.mem.readW (w64 p.W + BitVec.ofNat 64 8) 32)
        (t.mem.readW (w64 p.W + BitVec.ofNat 64 12) 32 ||| 0x80000000#32)) (w64 p.W + BitVec.ofNat 64 96) 16 := by
    rw [hm₁, headMem]
    exact Proof.AesGcm.X86.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Region.contains_self _ _)) (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  obtain hicb : bytesAt t₁.mem (w64 p.W + BitVec.ofNat 64 96) 16 =
      Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16) := by
    rw [hcb, Proof.Cmac.bytesAt_store4, BitVec.add_zero, ← GcmSiv.Words32.initialCounter_words,
      Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW, Proof.Cmac.le4_readW,
      ← Proof.Cmac.bytesAt_split4]
  obtain h4 := Proof.Cmac.bytesAt_add t₁.mem (w64 p.W + BitVec.ofNat 64 96) 4 12
  rw [show 4 + 12 = 16 from rfl, hicb, add_ofNat_assoc] at h4
  obtain C₀ : CtrSt (w64 p.W) (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) 0 t₁.mem := by
    refine ⟨?_, ?_⟩
    · rw [GcmSiv.readW32_leNat, Nat.add_zero, h4, List.take_left' (Proof.Cmac.bytesAt_length _ _ _)]
    · rw [h4, List.drop_left' (Proof.Cmac.bytesAt_length _ _ _)]
  obtain fm₁ : Frame (cryR p) t.mem t₁.mem := f₁.sub fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 96, 32⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨w64 p.W + BitVec.ofNat 64 176, 8⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  obtain E₁ : Env p t₁ := E.mut L bp₁ sp₁ rd₁ wr₁ (frame_toMut fm₁ (inMut_cryR p))
  obtain n₁ : slotv t₁.mem p.W nO = BitVec.ofNat 32 p.n := by rw [slotv_eq, hm₁, headMem, Mem.readW_writeW_self32]
  exact ⟨t₁, run₁, E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩

theorem crypt_ok (v : GcmImpl) {p : Prm} (L : Lay p) {t : State} (E : Env p t) :
    WP isa (crypt v.callees) t (CryptPost p t) := by
  have hw := L.ww
  have hn := L.n32
  obtain ⟨t₁, run₁, ⟨E₁, rd₁, wr₁, si₁, z₁, n₁, C₀, hx₁, hc₁, fm₁⟩⟩ := cryptStart_ok L E
  obtain hcl : ∀ y, (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R y).length = 16 :=
    GcmSiv.ctxCiph_length _ _ _
  obtain hxl : (bytesAt t.mem (w64 p.D) p.n).length = p.n := Proof.Cmac.bytesAt_length _ _ _
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  -- The whole blocks.
  obtain hmid : WP isa (.ite .e (.block []) (.loop (cryptBlock v.callees) .ne)) t₁
      (BlocksPost p (Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R)
        (Spec.GcmSiv.initialCounter (bytesAt t.mem (w64 p.W) 16)) (bytesAt t.mem (w64 p.D) p.n) (p.n / 16) t₁) := by
    refine WP.ite (decide (p.n / 16 = 0)) (eval_e z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : p.n / 16 = 0 := by simpa using ht
      refine WP.block_nil ?_
      rw [h0]
      exact ⟨E₁, rfl, rfl, by rw [si₁, Nat.mul_zero, BitVec.add_zero], by rw [n₁, Nat.mul_zero, Nat.sub_zero], C₀,
        by rw [Nat.mul_zero, GcmSiv.ctrPart_zero, hx₁], Frame.refl _ _⟩
    · have h0 : p.n / 16 ≠ 0 := by simpa using hf
      exact blocks_ok v L E₁ hxl (by omega_arith) si₁ n₁ C₀ hx₁ hc₁
  refine WP.seq (WP.mono hmid fun t₂ B => ?_)
  obtain n₂ : slotv t₂.mem p.W nO = BitVec.ofNat 32 (p.n % 16) := by rw [B.n]; congr 1; omega_arith
  obtain ⟨t₃, run₃, z₃, E₃, si₃, m₃, rd₃, wr₃⟩ := anyLeft_ok L B.env (by omega_arith) n₂
  refine WP.seq (WP.of_runBlock ⟨t₃, run₃, ?_⟩)
  refine WP.ite (decide (p.n % 16 = 0)) (eval_e z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : p.n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨E₃, by rw [rd₃, B.rd, rd₁], by rw [wr₃, B.wr, wr₁], by rw [m₃]; exact fm₁.trans B.frame, ?_⟩
    rw [m₃, B.data, show 16 * (p.n / 16) = p.n by omega_arith, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]
  · have h0 : p.n % 16 ≠ 0 := by simpa using hf
    obtain hc₂ : Spec.GcmSiv.ctxCiph t₃.mem (w64 p.W + BitVec.ofNat 64 512) p.R =
        Spec.GcmSiv.ctxCiph t.mem (w64 p.W + BitVec.ofNat 64 512) p.R := by
      rw [m₃, ciph_cryR L B.frame, hc₁]
    refine WP.mono (cryptTail_ok v L E₃ hxl (b := p.n / 16) (r := p.n % 16) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [si₃, B.esi]) (by rw [slotv_eq, m₃]; exact n₂) (m₃ ▸ B.ctr) (by rw [m₃]; exact B.data) hc₂)
      fun t₄ T => ?_
    refine ⟨T.env, by rw [T.rd, rd₃, B.rd, rd₁], by rw [T.wr, wr₃, B.wr, wr₁],
      (fm₁.trans (m₃ ▸ B.frame)).trans T.frame, ?_⟩
    rw [T.data, GcmSiv.ctrPart_all _ hcl _ _ (by rw [hxl])]

end VG.Proof.AesGcmSiv.X86

end

end

/-! ### `AesGcmSiv.X86.Entry`, which this module and modules that import it used -/

section

/-! ### `AesGcmSiv.X86.Contract`, which only this module used -/

section

/-!
# AES-GCM-SIV on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The code is proved with its
working space as a ninth argument, `work`, against the shared contracts
with it appended (`Proof/AesGcmSiv/Scratch.lean`), which imply these
(`Verified.lean`); a frame allocates it (`Frame.lean`). The arguments are on
the stack, from `[esp + 4]` (cdecl), and may be overwritten (`writeArgs`);
the calls of `vg_aes_ctr32_to`, `vg_aes_expand_key` and `vg_ghash`, which make
no calls, push their arguments and return addresses in the 32 bytes below
`esp`, which no buffer overlaps, nor the return address.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.GcmSiv (ctxCiph keyLen encryptWith decryptWith zeros)

/-- The buffers of `vg_aes_gcm_siv_seal(schedule, rounds, nonce, aad, aad_len, data, len, tag, work)`
and `vg_aes_gcm_siv_open`, with the same arguments. -/
abbrev schR (s : State) : Region := ⟨(arg s 0).setWidth 64, 240⟩
abbrev nonceR (s : State) : Region := ⟨(arg s 2).setWidth 64, 12⟩
abbrev aadR (s : State) : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
abbrev dataR (s : State) : Region := ⟨(arg s 5).setWidth 64, (arg s 6).toNat⟩
abbrev tagR (s : State) : Region := ⟨(arg s 7).setWidth 64, 16⟩
abbrev workR (s : State) : Region := ⟨(arg s 8).setWidth 64, 2816⟩
abbrev argsR' (s : State) : Region := ⟨argAddr s 0, 36⟩
abbrev retR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
abbrev stackR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩

/-- What both functions' preconditions say of the buffers and the
arguments, but for which may be written. -/
def oneLay (s : State) : Prop :=
  (schR s).Disjoint (dataR s) ∧ (schR s).Disjoint (workR s) ∧ (schR s).Disjoint (argsR' s) ∧
  (nonceR s).Disjoint (dataR s) ∧ (nonceR s).Disjoint (workR s) ∧ (nonceR s).Disjoint (argsR' s) ∧
  (aadR s).Disjoint (dataR s) ∧ (aadR s).Disjoint (workR s) ∧ (aadR s).Disjoint (argsR' s) ∧
  (dataR s).Disjoint (tagR s) ∧ (dataR s).Disjoint (workR s) ∧ (dataR s).Disjoint (argsR' s) ∧
  (tagR s).Disjoint (workR s) ∧ (tagR s).Disjoint (argsR' s) ∧ (workR s).Disjoint (argsR' s) ∧
  (retR s).Disjoint (schR s) ∧ (retR s).Disjoint (nonceR s) ∧ (retR s).Disjoint (aadR s) ∧
  (retR s).Disjoint (dataR s) ∧ (retR s).Disjoint (tagR s) ∧ (retR s).Disjoint (workR s) ∧
  (retR s).Disjoint (argsR' s) ∧
  (stackR s).Disjoint (schR s) ∧ (stackR s).Disjoint (nonceR s) ∧ (stackR s).Disjoint (aadR s) ∧
  (stackR s).Disjoint (dataR s) ∧ (stackR s).Disjoint (tagR s) ∧ (stackR s).Disjoint (workR s) ∧
  (stackR s).Disjoint (argsR' s) ∧
  (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 12 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32 ∧
  (arg s 7).toNat + 16 ≤ 2 ^ 32 ∧ (arg s 8).toNat + 2816 ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 14)

/-- `seal` writes the tag. -/
def sealPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s] ∧ s.wr = [dataR s, tagR s, workR s, argsR' s] ∧ oneLay s

/-- `open` reads it. -/
def openPre (s : State) : Prop :=
  s.rd = [schR s, nonceR s, aadR s, tagR s] ∧ s.wr = [dataR s, workR s, argsR' s] ∧ oneLay s

/-- All nine stack arguments are public, and the stack pointer. -/
def onePub (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 9, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_siv_seal`. -/
def sealX86 : Contract isa where
  pre := sealPre
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
        (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) =
      (bytesAt s'.mem ((arg s 5).setWidth 64) (arg s 6).toNat, bytesAt s'.mem ((arg s 7).setWidth 64) 16)
  pub := onePub

/-- What `vg_aes_gcm_siv_open` computes, for the state `s`. -/
abbrev openResult (s : State) : Option (List Byte) :=
  decryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (keyLen (arg s 1).toNat)
    (bytesAt s.mem ((arg s 2).setWidth 64) 12) (bytesAt s.mem ((arg s 5).setWidth 64) (arg s 6).toNat)
    (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) (bytesAt s.mem ((arg s 7).setWidth 64) 16)

/-- What `vg_aes_gcm_siv_open` leaves in `eax` and in the `n` bytes of data
at `D`, for the result `r`. Irreducible, so that checking a state against
it never evaluates `r`. -/
@[irreducible] def openPost (r : Option (List Byte)) (s' : State) (D : Addr) (n : Nat) : Prop :=
  match r with
  | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem D n = pt
  | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem D n = zeros n

theorem openPost_some {r : Option (List Byte)} {pt : List Byte} {s' : State} {D : Addr} {n : Nat}
    (hr : r = some pt) (hax : s'.gpr .eax = 1) (hd : bytesAt s'.mem D n = pt) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

theorem openPost_none {r : Option (List Byte)} {s' : State} {D : Addr} {n : Nat}
    (hr : r = none) (hax : s'.gpr .eax = 0) (hd : bytesAt s'.mem D n = zeros n) : openPost r s' D n := by
  subst hr; unfold openPost; exact ⟨hax, hd⟩

/-- `vg_aes_gcm_siv_open`. It does not branch on whether the tag is right,
so its runs are related without the leak the shared contract allows. -/
def openX86 : Contract isa where
  pre := openPre
  post s s' := openPost (openResult s) s' ((arg s 5).setWidth 64) (arg s 6).toNat
  pub := onePub

end VG.Proof.AesGcmSiv.X86

end

end


/-!
# AES-GCM-SIV on x86: the arguments and the entry

Untrusted: everything here is checked by Lean. The precondition `onePre`
gives the public arguments (`prmOf`), how they lie (`lay_of`) and what the
state may access (`perm_of`). The entry saves our caller's registers in `W`
(AES-GCM's `save_ok`) and copies the stack arguments into their slots
(`keeps_ok`): after it, `Env` holds (`entry_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcmSiv.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp keep entry saveAt)
open VG.Proof.AesGcm.X86 (w64 slotv argA argsR argsR_eq argA_contains argA_sub SavedAt save_ok KeepEnv keeps_ok
  keepR runBlock_app_of in_off below_eq covers_left)

/-- What both preconditions say: the layout, and that the buffers may be
read (the key schedule, the nonce, the additional data and the tag) or
written (the data, `work` and the arguments). -/
structure onePre (s : State) : Prop where
  lay : oneLay s
  rd : ∀ r ∈ [schR s, nonceR s, aadR s, tagR s], Covers [r] (s.rd ++ s.wr)
  wr : ∀ r ∈ [dataR s, workR s, argsR' s], Covers [r] s.wr

theorem onePre_seal {s : State} (h : sealPre s) : onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => ?_, fun r hr => ?_⟩
  swap
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact covers_of_mem (by rw [hwr]; simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  · exact covers_of_mem (List.mem_append_right _ (by rw [hwr]; simp))

theorem onePre_open {s : State} (h : openPre s) : onePre s := by
  obtain ⟨hrd, hwr, hl⟩ := h
  refine ⟨hl, fun r hr => covers_of_mem (List.mem_append_left _ (by rw [hrd]; exact hr)),
    fun r hr => covers_of_mem (by rw [hwr]; exact hr)⟩

/-- The public arguments of a state. -/
def prmOf (s : State) : Prm where
  K := arg s 0
  W := arg s 8
  N := arg s 2
  A := arg s 3
  D := arg s 5
  T := arg s 7
  SP := s.gpr .esp
  R := (arg s 1).toNat
  al := (arg s 4).toNat
  n := (arg s 6).toNat

/-- What the precondition says of the stack arguments. -/
structure ArgsOk (s : State) : Prop where
  rA : Covers [argsR (s.gpr .esp) 9] (s.rd ++ s.wr)
  aw : (argsR (s.gpr .esp) 9).Disjoint ⟨w64 (arg s 8), 2816⟩
  fa : (s.gpr .esp).toNat + 4 + 4 * 9 ≤ 2 ^ 32

theorem lay_of {s : State} (h : onePre s) : Lay (prmOf s) := by
  obtain ⟨sd, sw, _, nd, nw, _, ad, aw, _, dt, dw, _, tw, _, _, _, _, _, rd, rt, rw, _, bs, bn, ba, bd, bt, bw, _,
    fK, fN, fA, fD, fT, fW, sp32, _, hR⟩ := h.lay
  simp only [stackR] at bs bn ba bd bt bw
  rw [show (32 : Addr) = BitVec.ofNat 64 32 from rfl, below_eq sp32] at bs bn ba bd bt bw
  exact ⟨fK, fW, fN, fA, fD, fT, sp32, sw, sd, nw, nd, aw, ad, dw, tw, dt.symm, bs, bn, ba, bd, bw, bt, hR,
    BitVec.isLt _, BitVec.isLt _, rw, rd, rt⟩

theorem perm_of {s : State} (h : onePre s) : Perm (prmOf s) s :=
  ⟨h.rd (schR s) (by simp), h.rd (nonceR s) (by simp), h.rd (aadR s) (by simp), h.wr (dataR s) (by simp),
    h.wr (workR s) (by simp), h.rd (tagR s) (by simp)⟩

theorem argsOk_of {s : State} (h : onePre s) : ArgsOk s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, wa, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, spf, -⟩ := h.lay
  refine ⟨?_, ?_, by omega_using [spf]⟩
  · rw [argsR_eq]; exact covers_left (h.wr (argsR' s) (by simp))
  · rw [argsR_eq]; exact wa.symm

/-- The arguments the entry copies, and where. -/
abbrev entryPs : List (Nat × Nat) :=
  [(0, ctxO), (1, roundsO), (2, nonceO), (3, aadO), (4, alenO), (5, dataO), (6, lenO), (7, tpO)]

theorem sivEntry_eq : sivEntry = entry 8 (entryPs.flatMap (fun p => keep p.1 p.2)) := rfl

/-- What the entry leaves. -/
structure Entered (s : State) (p : Prm) (s' : State) : Prop where
  env : Env p s'
  saved : SavedAt s'.mem p.W s
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [⟨w64 p.W + BitVec.ofNat 64 128, 48⟩] s.mem s'.mem

/-- The entry. -/
theorem entry_ok {s : State} (h : onePre s) : WP isa sivEntry s (Entered s (prmOf s)) := by
  have L := lay_of h
  have P := perm_of h
  have Ao := argsOk_of h
  rw [sivEntry_eq]
  generalize hSP : s.gpr .esp = SP at Ao
  have rA := Ao.rA
  have aw := Ao.aw
  have fa := Ao.fa
  rw [hSP] at rA aw fa
  have fw : (arg s 8).toNat + 2560 ≤ 2 ^ 32 := by have := L.ww; simp only [prmOf] at this; omega_using [this]
  have wW : Covers [⟨w64 (arg s 8), 2560⟩] s.wr := P.w2560
  have i₀ : InRegions (s.rd ++ s.wr) (argA SP 8) 4 := rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) fa⟩
  refine WP.seq (WP.of_runBlock ⟨_, by grun [hSP, i₀], ?_⟩)
  have hax : (s.setReg .eax (s.mem.readW (argA SP 8) 32)).gpr .eax = arg s 8 := by
    rw [gpr_setReg_self, ← hSP]; rfl
  let s₀ := s.setReg .eax (s.mem.readW (argA SP 8) 32)
  try rewrite [show s.setReg .eax (s.mem.readW (argA SP 8) 32) = s₀ from rfl] at *
  have hs₀ : s₀ = s.setReg .eax (s.mem.readW (argA SP 8) 32) := rfl
  obtain ⟨s₁, run₁, bp₁, g₁, rd₁, wr₁, sv₁, f₁⟩ := save_ok s₀ hax (by rw [hs₀]; exact wW) fw
  have sp₁ : s₁.gpr .esp = SP := by rw [g₁ _ (by decide), hs₀, gpr_setReg_of_ne _ _ (by decide), hSP]
  have argW : ∀ {i}, i < 9 → ∀ {d k : Nat}, d + k ≤ 2816 →
      ∀ r ∈ [(⟨w64 (arg s 8) + BitVec.ofNat 64 d, k⟩ : Region)], (⟨argA SP i, 4⟩ : Region).Disjoint r :=
    fun hi _ _ hk r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (aw.sub_left (argA_sub hi fa)).sub_right (Lay.wSub hk)
  have hA₁ : ∀ i < 9, s₁.mem.readW (argA SP i) 32 = arg s i := fun i hi => by
    rw [f₁.readW (r := ⟨argA SP i, 4⟩) (Region.contains_self _ _) (argW hi (by decide)) (by decide)]
    rw [arg, argAddr, hSP]
    exact rfl
  have aw' : (argsR SP 9).Disjoint ⟨w64 (arg s 8), 2560⟩ := aw.sub_right (Region.sub_prefix (by decide))
  have ke : KeepEnv (arg s 8) SP 9 s₁ := ⟨bp₁, sp₁, by rw [wr₁]; exact wW, by rw [rd₁, wr₁]; exact rA, aw', fa, fw⟩
  obtain ⟨s₃, run₃, sl₃, f₃, g₃, rd₃, wr₃⟩ := keeps_ok entryPs (fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (by decide) ke
  have bp₃ : s₃.gpr .ebp = arg s 8 := by rw [g₃ _ (by decide), bp₁]
  have sp₃ : s₃.gpr .esp = SP := by rw [g₃ _ (by decide), sp₁]
  refine WP.of_runBlock ⟨_, runBlock_app_of run₁ run₃, ?_⟩
  -- What the entry wrote.
  have f₃' : Frame [⟨w64 (arg s 8) + BitVec.ofNat 64 128, 48⟩] s.mem s₃.mem := by
    refine (f₁.sub fun r hr => ?_).trans (f₃.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
  have hsv : SavedAt s₃.mem (arg s 8) s := by
    have := sv₁.frame f₃ fun r hr => by
      simp only [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    obtain ⟨a, b, c, d⟩ := this
    refine ⟨a.trans ?_, b.trans ?_, c.trans ?_, d.trans ?_⟩ <;>
      simp only [hs₀, gpr_setReg_of_ne _ _ (by decide : Reg.ebx ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.esi ≠ .eax),
        gpr_setReg_of_ne _ _ (by decide : Reg.edi ≠ .eax), gpr_setReg_of_ne _ _ (by decide : Reg.ebp ≠ .eax)]
  have sl : ∀ q ∈ entryPs, slotv s₃.mem (arg s 8) q.2 = arg s q.1 := fun q hq => by
    have e := sl₃ q hq
    have hq1 : q.1 < 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [hA₁ q.1 hq1] at e
    exact e
  have ofN : ∀ x : BitVec 32, BitVec.ofNat 32 x.toNat = x := fun x => BitVec.eq_of_toNat_eq (by simp)
  refine ⟨⟨bp₃, by rw [sp₃, ← hSP]; rfl, P.of_eq (by rw [rd₃, rd₁]; rfl) (by rw [wr₃, wr₁]; rfl),
    ⟨sl (0, ctxO) (by simp), by simp only [prmOf]; rw [sl (1, roundsO) (by simp)]; exact (ofN _).symm,
      sl (2, nonceO) (by simp), sl (3, aadO) (by simp),
      by simp only [prmOf]; rw [sl (4, alenO) (by simp)]; exact (ofN _).symm, sl (5, dataO) (by simp),
      by simp only [prmOf]; rw [sl (6, lenO) (by simp)]; exact (ofN _).symm, sl (7, tpO) (by simp)⟩⟩, hsv, by rw [rd₃, rd₁]; rfl, by rw [wr₃, wr₁]; rfl, f₃'⟩

end VG.Proof.AesGcmSiv.X86

end

end

/-! ### `AesGcmSiv.X86.Seal`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_seal` (correctness)

Untrusted: everything here is checked by Lean. The entry, the keys, POLYVAL
and the tag input, the tag at `W`, counter mode on the data from it, the tag
copied out to `tag` and the restore compute `encryptWith` (RFC 8452 §4) of
the arguments (`seal_wp`), given that the tag input computed with GHASH is
the RFC's (`Proof.GcmSiv.Words.tagInputG`, related to it by
`Proof.GcmSiv.Polyval.tagInput_eq_tagInputG`). Each
piece writes only `mutR`, which keeps the slots, our caller's registers,
the return address, the key schedule, the nonce and the additional data.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left)

/-- The tag input of RFC 8452 is the one computed with GHASH. -/
abbrev TagInputEq : Prop := ∀ a n pt d : List Byte, Spec.GcmSiv.tagInput a n pt d = tagInputG a n pt d

/-- The end: our caller's registers restored. -/
theorem exit_ok {p : Prm} (L : Lay p) {s₀ t : State} (E : Env p t) (hsp : p.SP = s₀.gpr .esp)
    (hs : SavedAt t.mem p.W s₀) (hret : t.mem.readW (w64 p.SP) 32 = s₀.mem.readW (w64 p.SP) 32) :
    WP isa (.block Impl.AesGcm.X86.restore) t fun s' => abiPreserved s₀ s' ∧ s'.mem = t.mem ∧
      s'.gpr .eax = t.gpr .eax :=
  WP.mono (Proof.AesGcm.X86.exit_ok E.ebp (by rw [E.esp, hsp]) (covers_left E.perm.w2560)
    (by have := L.ww; omega_using [this]) hs (by rw [← hsp]; exact hret)) fun _ ⟨a, m, r, _⟩ => ⟨a, m, r⟩

/-- What the entry wrote is in our caller's registers and the slots. -/
theorem entered_mut {s : State} {p : Prm} {s₁ : State} (L : Lay p) (En : Entered s p s₁) :
    s₁.mem.readW (w64 p.SP) 32 = s.mem.readW (w64 p.SP) 32 ∧
      Spec.GcmSiv.ctxCiph s₁.mem (w64 p.K) p.R = Spec.GcmSiv.ctxCiph s.mem (w64 p.K) p.R ∧
      bytesAt s₁.mem (w64 p.N) 12 = bytesAt s.mem (w64 p.N) 12 ∧
      bytesAt s₁.mem (w64 p.A) p.al = bytesAt s.mem (w64 p.A) p.al ∧
      bytesAt s₁.mem (w64 p.D) p.n = bytesAt s.mem (w64 p.D) p.n ∧
      bytesAt s₁.mem (w64 p.W) 16 = bytesAt s.mem (w64 p.W) 16 := by
  have f := En.frame
  obtain d : ∀ {P : Addr} {k : Nat}, (⟨P, k⟩ : Region).Disjoint ⟨w64 p.W, 2816⟩ →
      ∀ r ∈ [(⟨w64 p.W + BitVec.ofNat 64 128, 48⟩ : Region)], (⟨P, k⟩ : Region).Disjoint r := fun h r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.sub_right (Lay.wSub (by decide))
  refine ⟨Proof.AesGcm.X86.ret_kept f (d L.retW), ?_, Proof.AesGcm.X86.bytesAt_frame f (d L.n_w) (by decide),
    Proof.AesGcm.X86.bytesAt_frame f (d L.a_w) (by have := L.al32; omega_using [this]),
    Proof.AesGcm.X86.bytesAt_frame f (d L.d_w) (by have := L.n32; omega_using [this]),
    Proof.AesGcm.X86.bytesAt_frame f (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      simpa using Lay.w_w (W := p.W) (a := 0) (n := 16) (d := 128) (k := 48) (.inl (by decide)) (by decide)
        (by decide)) (by decide)⟩
  unfold Spec.GcmSiv.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame f (d (L.k_w.sub_left (Region.sub_prefix L.rounds_le)))
    (by have := L.rounds_le; omega_using [this])]

/-- `vg_aes_gcm_siv_seal`. -/
theorem seal_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : sealPre s) :
    WP isa («seal» v.callees) s fun s' => abiPreserved s s' ∧ sealX86.post s s' := by
  obtain h := onePre_seal hs
  obtain tW : Covers [⟨w64 (prmOf s).T, 16⟩] s.wr := covers_of_mem (by rw [hs.2.1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₁ En => ?_)
  obtain ⟨ret₁, hK₁, n₁, a₁, d₁, -⟩ := entered_mut L En
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L En.env) fun s₂ Ky => ?_)
  obtain f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- POLYVAL and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Ky.env Ky.hkey Ky.acc) fun s₃ Po => ?_)
  obtain f₃ := frame_toMut Po.frame (inMut_polyR _)
  -- The tag.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 0) (by decide)) fun s₄ Tg => ?_)
  obtain f₄ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- Counter mode.
  refine WP.seq (WP.mono (crypt_ok v L Tg.env) fun s₅ Cr => ?_)
  obtain f₅ := frame_toMut Cr.frame (inMut_cryR _)
  obtain f₂₅ := (f₂.trans f₃).trans (f₄.trans f₅)
  -- The tag copied out.
  obtain tW₅ : Covers [⟨w64 (prmOf s).T, 16⟩] s₅.wr := by rw [Cr.wr, Tg.wr, Po.wr, Ky.wr, En.wr]; exact tW
  refine WP.seq (WP.mono (tagOut_ok L Cr.env tW₅) fun s₆ ⟨tg₆, f₆, bp₆, sp₆, _, rd₆, wr₆⟩ => ?_)
  obtain E₆ := Cr.env.tag L bp₆ sp₆ rd₆ wr₆ f₆
  obtain sv₆ : SavedAt s₆.mem (prmOf s).W s :=
    (SavedAt.mut L f₂₅ En.saved).frame f₆ (w_t L (d := 128) (k := 16) (by decide))
  obtain rT : ∀ q ∈ [(⟨w64 (prmOf s).T, 16⟩ : Region)], (⟨w64 (prmOf s).SP, 4⟩ : Region).Disjoint q :=
    fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact L.retT
  obtain ret₆ : s₆.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [Proof.AesGcm.X86.ret_kept f₆ rT, ret_mut L f₂₅, ret₁]
  obtain d₆ : bytesAt s₆.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n :=
    Proof.AesGcm.X86.bytesAt_frame f₆ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_d.symm) (by omega_using [hn])
  -- `restore`.
  refine WP.mono (exit_ok L E₆ rfl sv₆ ret₆) fun s' ⟨ga, hm, _⟩ => ⟨ga, ?_⟩
  show Spec.GcmSiv.encryptWith (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
      (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al) =
    (bytesAt s'.mem (w64 (prmOf s).D) (prmOf s).n, bytesAt s'.mem (w64 (prmOf s).T) 16)
  rw [hm, d₆, tg₆]
  -- What the pieces read.
  obtain n₂ : bytesAt s₂.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L f₂, n₁]
  obtain a₂ : bytesAt s₂.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L f₂, a₁]
  obtain dk₂ : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dk₂ (by omega_using [hn]), d₁]
  obtain d₄ : bytesAt s₄.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega_using [hn]),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega_using [hn]), d₂]
  obtain dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain key₃ : Spec.GcmSiv.ctxCiph s₃.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine dS (fun r hr => ?_) Po.frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain key₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    refine (dS (fun r hr => ?_) Tg.frame).trans key₃
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain t₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 := by
    refine Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.d_w' (by decide)).symm
    · exact (L.bw' (by decide)).symm
  rw [BitVec.add_zero] at t₅
  have tg := Tg.out
  rw [BitVec.add_zero] at tg
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have po := Po.out
  rw [n₂, a₂, d₂] at po
  rw [Cr.data, t₅, d₄, key₄, ci, tg, key₃, ci, po, ← au]
  unfold Spec.GcmSiv.encryptWith
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

end VG.Proof.AesGcmSiv.X86

end

end

/-!
# AES-GCM-SIV on x86: `vg_aes_gcm_siv_open` (correctness)

Untrusted: everything here is checked by Lean. The entry, the received tag
copied to `W`, the keys, counter mode on the data from it, POLYVAL of the
result and the tag input, its tag at `W + 240`, the comparison, the mask and
the restore compute `decryptWith` (RFC 8452 §5) of the arguments (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86

open VG VG.X86 VG.Impl.AesGcmSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.GcmSiv.Words (tagInputG)
open VG.Proof.AesGcm.X86 (w64 SavedAt GcmImpl covers_left length_bytesAt)

theorem decrypt_eq (hti : TagInputEq) (ciph : Spec.GcmSiv.Cipher) (kl : Nat) (nonce ct aad tag : List Byte) :
    Spec.GcmSiv.decryptWith ciph kl nonce ct aad tag =
      let dk := Spec.GcmSiv.deriveKeys ciph kl nonce
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 nonce
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct) aad) = tag then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter tag) ct)
      else none := by
  unfold Spec.GcmSiv.decryptWith
  generalize Spec.GcmSiv.deriveKeys ciph kl nonce = dk
  obtain ⟨a, e⟩ := dk
  simp only [hti]

/-- Counter mode after the keys keeps what POLYVAL starts from. -/
theorem keys_crypt {p : Prm} (L : Lay p) {σ s₂ s₃ : State} (Ky : KeysPost p σ s₂) (Cr : CryptPost p s₂ s₃) :
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 64) =
      GcmSiv.Words.hkeyOf (Spec.GcmSiv.ofBytes (bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16)) ∧
    Spec.Gcm.blockAt s₃.mem (w64 p.W + BitVec.ofNat 64 80) = 0 ∧
    bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 := by
  obtain dCr : ∀ {d : Nat}, 16 ≤ d → d + 16 ≤ 96 → ∀ r ∈ cryR p,
      (⟨w64 p.W + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact Lay.w_w (.inl (by omega_using [h₂])) (by omega_using [h₂]) (by decide)
    · exact (L.d_w' (by omega_using [h₂])).symm
    · exact (L.bw' (by omega_using [h₂])).symm
  obtain a₃ : bytesAt s₃.mem (w64 p.W + BitVec.ofNat 64 16) 16 = bytesAt s₂.mem (w64 p.W + BitVec.ofNat 64 16) 16 :=
    Proof.AesGcm.X86.bytesAt_frame Cr.frame (dCr (by decide) (by decide)) (by decide)
  refine ⟨?_, ?_, a₃⟩
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.hkey, a₃]
  · rw [Proof.AesGcm.X86.blockAt_frame Cr.frame (dCr (by decide) (by decide)), Ky.acc]

/-- `vg_aes_gcm_siv_open`. -/
theorem open_wp (v : GcmImpl) (hti : TagInputEq) {s : State} (hs : openPre s) :
    WP isa («open» v.callees) s fun s' => abiPreserved s s' ∧ openX86.post s s' := by
  obtain h := onePre_open hs
  obtain L := lay_of h
  have hRb := L.rounds_le
  have hn := L.n32
  refine WP.seq (WP.mono (entry_ok h) fun s₀ En => ?_)
  obtain ⟨ret₀, hK₀, n₀, a₀, d₀, -⟩ := entered_mut L En
  -- The received tag.
  refine WP.seq (WP.mono (recvTag_ok L En.env) fun s₁ ⟨E₁, tg₁, fr₁, _, _⟩ => ?_)
  obtain fr₁' : Frame (mutR (prmOf s)) s₀.mem s₁.mem := frame_toMut fr₁ fun q hq => by
    simp only [List.mem_singleton] at hq; subst hq
    simpa using inMut_w (prmOf s) (d := 0) (k := 16) (.inl (by decide))
  obtain ret₁ : s₁.mem.readW (w64 (prmOf s).SP) 32 = s.mem.readW (w64 (prmOf s).SP) 32 := by
    rw [ret_mut L fr₁', ret₀]
  obtain hK₁ := (ciph_mut L fr₁').trans hK₀
  obtain n₁ := (nonce_mut L fr₁').trans n₀
  obtain a₁ := (aad_mut L fr₁').trans a₀
  obtain d₁ : bytesAt s₁.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n :=
    (Proof.AesGcm.X86.bytesAt_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.d_w.sub_right (Region.sub_prefix (by decide)))
      (by omega_using [hn])).trans d₀
  obtain tag₁ : bytesAt s₁.mem (w64 (prmOf s).W) 16 = bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [tg₁]
    exact Proof.AesGcm.X86.bytesAt_frame En.frame (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact L.t_w.sub_right (Lay.wSub (by decide))) (by decide)
  obtain sv₁ := SavedAt.mut L fr₁' En.saved
  -- The keys.
  refine WP.seq (WP.mono (keys_ok v L E₁) fun s₂ Ky => ?_)
  obtain f₂ := frame_toMut Ky.frame (inMut_keyR _)
  -- Counter mode from the received tag.
  refine WP.seq (WP.mono (crypt_ok v L Ky.env) fun s₃ Cr => ?_)
  obtain f₃ := frame_toMut Cr.frame (inMut_cryR _)
  obtain ⟨hG₃, hY₃, a₃⟩ := keys_crypt L Ky Cr
  -- POLYVAL of the plaintext and the tag input.
  refine WP.seq (WP.mono (polyval_ok v L Cr.env hG₃ hY₃) fun s₄ Po => ?_)
  obtain f₄ := frame_toMut Po.frame (inMut_polyR _)
  -- Its tag at `W + 240`.
  refine WP.seq (WP.mono (tag_ok v L Po.env (o := 240) (by decide)) fun s₅ Tg => ?_)
  obtain f₅ := frame_toMut Tg.frame (inMut_tagWr _ (by decide))
  -- The comparison.
  obtain ⟨s₆, run₆, ax₆, hm₆, bp₆, sp₆, rd₆, wr₆⟩ := cmp_ok L Tg.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  obtain E₆ : Env (prmOf s) s₆ := Tg.env.keep (by rw [bp₆, Tg.env.ebp]) (by rw [sp₆, Tg.env.esp]) rd₆ wr₆ hm₆
  obtain ax₆' : s₆.gpr .eax = BitVec.ofNat 32 (if decide (bytesAt s₅.mem (w64 (prmOf s).W) 16 =
      bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 240) 16) then 1 else 0) := by
    rw [ax₆]; simp only [okVal, decide_eq_true_eq]
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ ax₆') fun s₇ Mk => ?_)
  obtain fM : Frame (mutR (prmOf s)) s₆.mem s₇.mem := by
    rw [Mk.mem]
    exact frame_toMut (writeBytes_frame _ _ _ (by
      split <;> simp only [length_bytesAt, Spec.GcmSiv.zeros, List.length_replicate] <;>
        exact Region.contains_self _ _) : Frame [⟨w64 (prmOf s).D, (prmOf s).n⟩] _ _) fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact inMut_d _
  obtain f₂₇ : Frame (mutR (prmOf s)) s₁.mem s₇.mem := ((f₂.trans f₃).trans (f₄.trans f₅)).trans (hm₆ ▸ fM)
  -- The restore.
  refine WP.mono (exit_ok L Mk.env rfl (SavedAt.mut L f₂₇ sv₁) (by rw [ret_mut L f₂₇, ret₁]))
    fun s' ⟨ga, hm, hax⟩ => ⟨ga, ?_⟩
  -- What the pieces read.
  obtain n₃ : bytesAt s₃.mem (w64 (prmOf s).N) 12 = bytesAt s.mem (w64 (prmOf s).N) 12 := by
    rw [nonce_mut L (f₂.trans f₃), n₁]
  obtain a₃' : bytesAt s₃.mem (w64 (prmOf s).A) (prmOf s).al = bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al := by
    rw [aad_mut L (f₂.trans f₃), a₁]
  obtain dK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).D, (prmOf s).n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.d_w' (by decide)
    · exact L.bd.symm
  obtain d₂ : bytesAt s₂.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame dK (by omega_using [hn]), d₁]
  obtain tK : ∀ r ∈ keyR (prmOf s), (⟨w64 (prmOf s).W + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain tag₂ : bytesAt s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Ky.frame tK (by decide), BitVec.add_zero, tag₁]
  obtain tag₅ : bytesAt s₅.mem (w64 (prmOf s).W + BitVec.ofNat 64 0) 16 =
      bytesAt s.mem (w64 (prmOf s).T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.bw' (by decide)).symm) (by decide),
      Proof.AesGcm.X86.bytesAt_frame Cr.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
        · exact (L.d_w' (by decide)).symm
        · exact (L.bw' (by decide)).symm) (by decide), tag₂]
  rw [BitVec.add_zero] at tag₂ tag₅
  obtain dS : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 (prmOf s).W + BitVec.ofNat 64 512, 240⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' → Spec.GcmSiv.ctxCiph m' (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
        Spec.GcmSiv.ctxCiph m (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := fun hd m m' hf => by
    unfold Spec.GcmSiv.ctxCiph
    rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hRb)) (by omega_using [hRb])]
  obtain ci₄ : Spec.GcmSiv.ctxCiph s₄.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R =
      Spec.GcmSiv.ctxCiph s₂.mem (w64 (prmOf s).W + BitVec.ofNat 64 512) (prmOf s).R := by
    rw [dS (fun r hr => ?_) Po.frame, ciph_cryR L Cr.frame]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
    · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.bw' (by decide)).symm
  obtain d₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = bytesAt s₃.mem (w64 (prmOf s).D) (prmOf s).n := by
    rw [Proof.AesGcm.X86.bytesAt_frame Tg.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.d_w' (by decide)
        · exact L.bd.symm) (by omega_using [hn]),
      Proof.AesGcm.X86.bytesAt_frame Po.frame (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact L.d_w' (by decide)
        · exact absorbR_buf L.d_w L.bd r hr) (by omega_using [hn])]
  have au := Ky.auth
  have ci := Ky.ciph
  rw [hK₁, n₁] at au ci
  have pt₃ := Cr.data
  rw [tag₂, d₂, ci] at pt₃
  have po := Po.out
  rw [a₃, ← au, n₃, a₃', pt₃] at po
  have tg := Tg.out
  rw [ci₄, ci, po] at tg
  have md := Mk.mem
  rw [hm₆, tg, tag₅] at md
  obtain ax : s'.gpr .eax = s₆.gpr .eax := by rw [hax, Mk.eax]
  rw [ax₆', tg, tag₅] at ax
  show openPost (openResult s) s' (w64 (prmOf s).D) (prmOf s).n
  obtain hdec : openResult s =
      let dk := Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)
      if Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
          (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
            (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
          bytesAt s.mem (w64 (prmOf s).T) 16 then
        some (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n))
      else none := decrypt_eq hti _ _ _ _ _ _
  simp only at hdec
  obtain hD₅ : bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n = Spec.GcmSiv.ctr
      (Spec.GcmSiv.aes (Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
        (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12)).2)
      (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16)) (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n) := by
    rw [d₅, pt₃]
  obtain hl : ∀ c : Bool, (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n).length = (prmOf s).n := fun c => by
    cases c <;> simp [length_bytesAt, Spec.GcmSiv.zeros]
  obtain mD : ∀ c : Bool, bytesAt (writeBytes s₅.mem (w64 (prmOf s).D) (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n
      else Spec.GcmSiv.zeros (prmOf s).n)) (w64 (prmOf s).D) (prmOf s).n =
      if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n := fun c => by
    obtain e := Proof.AesGcm.X86.bytesAt_writeBytes_self s₅.mem (w64 (prmOf s).D)
      (if c then bytesAt s₅.mem (w64 (prmOf s).D) (prmOf s).n else Spec.GcmSiv.zeros (prmOf s).n)
      (by rw [hl]; omega_using [hn])
    rwa [hl] at e
  generalize Spec.GcmSiv.deriveKeys (Spec.GcmSiv.ctxCiph s.mem (w64 (prmOf s).K) (prmOf s).R)
    (Spec.GcmSiv.keyLen (prmOf s).R) (bytesAt s.mem (w64 (prmOf s).N) 12) = dk at ax hdec md hD₅
  rw [hdec]
  by_cases hc : Spec.GcmSiv.aes dk.2 (tagInputG dk.1 (bytesAt s.mem (w64 (prmOf s).N) 12)
      (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
        (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) =
      bytesAt s.mem (w64 (prmOf s).T) 16
  · refine openPost_some (ite_eq_left_of_eq_true _ _ (eq_true hc)) ?_ ?_
    · rw [ax, ite_eq_left (decide_eq_true hc.symm)]; rfl
    · rw [hm, md, mD, hD₅, ite_eq_left (decide_eq_true hc.symm)]
  · have hc' : ¬bytesAt s.mem (w64 (prmOf s).T) 16 = Spec.GcmSiv.aes dk.2 (tagInputG dk.1
        (bytesAt s.mem (w64 (prmOf s).N) 12)
        (Spec.GcmSiv.ctr (Spec.GcmSiv.aes dk.2) (Spec.GcmSiv.initialCounter (bytesAt s.mem (w64 (prmOf s).T) 16))
          (bytesAt s.mem (w64 (prmOf s).D) (prmOf s).n)) (bytesAt s.mem (w64 (prmOf s).A) (prmOf s).al)) :=
      Ne.symm hc
    refine openPost_none (ite_eq_right_of_eq_false _ _ (eq_false hc)) ?_ ?_
    · rw [ax, ite_eq_right (fun h => hc' (of_decide_eq_true h))]; rfl
    · rw [hm, md, mD, ite_eq_right (fun h => hc' (of_decide_eq_true h))]

end VG.Proof.AesGcmSiv.X86
