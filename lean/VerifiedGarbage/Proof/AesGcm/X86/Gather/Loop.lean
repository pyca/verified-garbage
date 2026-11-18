module

import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Impl.AesGcm.X86.SealGather
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Env
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Aes.X86.VariantProof
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Spec.Gcm.OutOfPlace
import VerifiedGarbage.Proof.Gcm.SealGather
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.Framework.PowLit

/-! ### `AesGcm.X86.Gather.Contract`, which this module and modules that import it used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: the contract

Untrusted: everything here is checked by Lean. The contract the proof of
`vg_aes_gcm_seal_gather` is written against, which the shared one
(`Proof.AesGcm.sealGatherRoundsContract`, with the 2688 bytes of stack below the stack
pointer that its frame and its call use) implies (`Gather/Verified.lean`):
cdecl, `(ctx, rounds, nonce, nonce_len, aad, aad_len, src, src_count, dst,
len, tag)` at `[esp + 4]` on, which the function may overwrite.
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (ctxCiph ctxH encryptWith gathered gatheredLen)

section
variable (s : State)

/-- The arguments. -/
abbrev K : BitVec 32 := arg s 0
abbrev Nn : BitVec 32 := arg s 2
abbrev NL : Nat := (arg s 3).toNat
abbrev Ad : BitVec 32 := arg s 4
abbrev AL : Nat := (arg s 5).toNat
abbrev Src : BitVec 32 := arg s 6
abbrev Cnt : Nat := (arg s 7).toNat
abbrev Dst : BitVec 32 := arg s 8
abbrev L : Nat := (arg s 9).toNat
abbrev Tg : BitVec 32 := arg s 10

/-- The regions: the key context, the nonce, the additional data, the
descriptors, the slices they list, the output, the tag, the arguments, the
return address and the stack below it. -/
abbrev kR : Region := ⟨w64 (K s), 256⟩
abbrev nR : Region := ⟨w64 (Nn s), NL s⟩
abbrev aR : Region := ⟨w64 (Ad s), AL s⟩
abbrev dsR : Region := ⟨w64 (Src s), Cnt s * 8⟩
abbrev lsR : List Region := Sig.listed 32 s.mem .u8 (w64 (Src s)) (Cnt s)
abbrev dR : Region := ⟨w64 (Dst s), L s⟩
abbrev tgR : Region := ⟨w64 (Tg s), 16⟩
abbrev argR : Region := ⟨argAddr s 0, 44⟩
abbrev retR : Region := ⟨w64 (s.gpr .esp), 4⟩
abbrev stkR : Region := ⟨w64 (s.gpr .esp) - BitVec.ofNat 64 2688, 2688⟩

/-- The total length of the first `i` slices, and their bytes. -/
abbrev gl (i : Nat) : Nat := gatheredLen 32 s.mem (w64 (Src s)) i
abbrev pt (i : Nat) : List Byte := gathered 32 s.mem (w64 (Src s)) i

end

/-- What the code of `vg_aes_gcm_seal_gather` needs. -/
def gatherPre (s : State) : Prop :=
  s.rd = [kR s, nR s, aR s, dsR s] ++ lsR s ∧ s.wr = [dR s, tgR s, argR s] ∧
    (kR s).Disjoint (dR s) ∧ (kR s).Disjoint (tgR s) ∧ (kR s).Disjoint (argR s) ∧
    (nR s).Disjoint (dR s) ∧ (nR s).Disjoint (tgR s) ∧ (nR s).Disjoint (argR s) ∧
    (aR s).Disjoint (dR s) ∧ (aR s).Disjoint (tgR s) ∧ (aR s).Disjoint (argR s) ∧
    (dR s).Disjoint (tgR s) ∧ (dR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (dR s).Disjoint r) ∧
    (dR s).Disjoint (argR s) ∧ (tgR s).Disjoint (dsR s) ∧ (∀ r ∈ lsR s, (tgR s).Disjoint r) ∧
    (tgR s).Disjoint (argR s) ∧ (dsR s).Disjoint (argR s) ∧ (∀ r ∈ lsR s, r.Disjoint (argR s)) ∧
    (retR s).Disjoint (kR s) ∧ (retR s).Disjoint (nR s) ∧ (retR s).Disjoint (aR s) ∧
    (retR s).Disjoint (dR s) ∧ (retR s).Disjoint (tgR s) ∧ (retR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (retR s).Disjoint r) ∧ (retR s).Disjoint (argR s) ∧
    (stkR s).Disjoint (kR s) ∧ (stkR s).Disjoint (nR s) ∧ (stkR s).Disjoint (aR s) ∧
    (stkR s).Disjoint (dR s) ∧ (stkR s).Disjoint (tgR s) ∧ (stkR s).Disjoint (dsR s) ∧
    (∀ r ∈ lsR s, (stkR s).Disjoint r) ∧ (stkR s).Disjoint (argR s) ∧
    (K s).toNat + 256 ≤ 2 ^ 32 ∧ (Nn s).toNat + NL s ≤ 2 ^ 32 ∧ (Ad s).toNat + AL s ≤ 2 ^ 32 ∧
    (Dst s).toNat + L s ≤ 2 ^ 32 ∧ (Tg s).toNat + 16 ≤ 2 ^ 32 ∧
    (Src s).toNat + Cnt s * 8 ≤ 2 ^ 32 ∧ (∀ r ∈ lsR s, r.base.toNat + r.len ≤ 2 ^ 32) ∧
    2688 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 48 ≤ 2 ^ 32 ∧
    ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧ gl s (Cnt s) = L s

/-- What two runs agree on: the stack pointer, the arguments and the descriptors. -/
def gatherPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 11, arg s₁ i = arg s₂ i) ∧
    ∀ i < Cnt s₁ * 8, s₁.mem (w64 (Src s₁) + BitVec.ofNat 64 i) = s₂.mem (w64 (Src s₁) + BitVec.ofNat 64 i)

/-- What `vg_aes_gcm_seal_gather` leaves: `sealGatherPost`. -/
def gatherPost (s s' : State) : Prop :=
  encryptWith (ctxCiph s.mem (w64 (K s)) (arg s 1).toNat) (ctxH s.mem (w64 (K s))) 16
      (bytesAt s.mem (w64 (Nn s)) (NL s)) (pt s (Cnt s)) (bytesAt s.mem (w64 (Ad s)) (AL s)) =
    (bytesAt s'.mem (w64 (Dst s)) (L s), bytesAt s'.mem (w64 (Tg s)) 16)

/-- `vg_aes_gcm_seal_gather`. -/
def gatherX86 : Contract isa where
  pre := gatherPre
  post := gatherPost
  pub := gatherPub

end VG.Proof.AesGcm.X86.Gather

end

end

/-! ### `AesGcm.X86.Gather.Copy`, which only this module used -/

section

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: copying a slice

Untrusted: everything here is checked by Lean. `copyWords` copies `k ≥ 1`
words from `edi` to `edx`, a word at a time through `eax`, counting `ecx`
down (`copyWords_ok`); with `copyLoop` for the last bytes (`copyLoop_ok`),
`copySlice` copies the slice that the descriptor at `esi` lists to `edx`,
leaving `edx` past it (`copySlice_wp`), in four steps the constant-time proof
uses too (`wordsArg_wp`, `words_wp`, `bytesArg_wp`, `bytes_wp`). The bytes
copied and the bytes written do not overlap.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)

/-- The registers the copy of a slice writes. -/
abbrev copyRegs : List Reg := [.eax, .ecx, .edx, .edi]

/-- What the copy of a slice keeps: the other registers and the permissions. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ copyRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

abbrev wordBody : List Instr :=
  [.mov .eax (.mem (at_ .edi 0)), .store (at_ .edx 0) .eax, .alu .add .edi (imm 4), .alu .add .edx (imm 4),
    .alu .sub .ecx (imm 1)]

theorem add4 (P : BitVec 32) (i : Nat) :
    P + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = P + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]

theorem wordStep_ok (s : State) {S D : BitVec 32} {i w : Nat} (hs : s.gpr .edi = S + BitVec.ofNat 32 (4 * i))
    (hd : s.gpr .edx = D + BitVec.ofNat 32 (4 * i)) (hn : s.gpr .ecx = BitVec.ofNat 32 w)
    (r : InRegions (s.rd ++ s.wr) (w64 (S + BitVec.ofNat 32 (4 * i))) 4)
    (wr : InRegions s.wr (w64 (D + BitVec.ofNat 32 (4 * i))) 4) :
    ∃ s', runBlock isa wordBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 (D + BitVec.ofNat 32 (4 * i))) (s.mem.readW (w64 (S + BitVec.ofNat 32 (4 * i))) 32) ∧
      s'.gpr .edi = S + BitVec.ofNat 32 (4 * (i + 1)) ∧ s'.gpr .edx = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      s'.gpr .ecx = BitVec.ofNat 32 w - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 w - BitVec.ofNat 32 1 == 0) ∧ Keeps s s' := by
  refine ⟨_, by xrun [wordBody, add_zero32, hs, hd, hn, r, wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setMem, gpr_setMem, mem_setReg, mem_arithFlags, gpr_setReg, ite_true]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hs, add4]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hd, add4]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hn]
  · simp only [zf_setMem, gpr_setMem, zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false,
      reduceCtorEq, hn]
  · refine ⟨fun r h => ?_, rfl, rfl⟩
    simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    simp [gpr_setMem, gpr_setReg, h₁, h₂, h₃, h₄]

/-- What the word loop needs: `k ≥ 1` words at `S` to copy to `D`, apart. -/
structure WordsPre (s : State) (S D : BitVec 32) (k : Nat) : Prop where
  edi : s.gpr .edi = S
  edx : s.gpr .edx = D
  ecx : s.gpr .ecx = BitVec.ofNat 32 k
  pos : 1 ≤ k
  fitS : S.toNat + 4 * k ≤ 2 ^ 32
  fitD : D.toNat + 4 * k ≤ 2 ^ 32
  rd : Covers [⟨w64 S, 4 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨w64 D, 4 * k⟩] s.wr
  disj : (⟨w64 S, 4 * k⟩ : Region).Disjoint ⟨w64 D, 4 * k⟩

/-- The bytes at `S + j`, not among the `j` bytes written at `D`, are what
they were. -/
theorem read_kept {m : Mem} {S D : Addr} {j n L : Nat} (hd : (⟨S, L⟩ : Region).Disjoint ⟨D, L⟩)
    (hj : j + n ≤ L) (hL : L < 2 ^ 64) :
    (writeBytes m D (bytesAt m S j)).read (S + BitVec.ofNat 64 j) n = m.read (S + BitVec.ofNat 64 j) n := by
  refine Mem.read_congr fun k hk => ?_
  refine (writeBytes_frame m D (bytesAt m S j) (R := ⟨D, j⟩)
    (by rw [Proof.Cmac.bytesAt_length]; exact Region.contains_self _ _)) _ fun r hr hcon => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [Offset.add_add] at hcon
  exact hd _ (Offset.contains_base S (show j + k + 1 ≤ L by omega_using [hj, hk]) (by omega_using [hj, hL, hk]))
    (Region.sub_prefix (show j ≤ L by omega_using [hj]) _ hcon)

/-- The 4 bytes of a read, as a list. -/
theorem read4_bytes (m : Mem) (a : Addr) :
    (List.range 4).map (fun j => (m.read a 4).extractLsb' (8 * j) 8) = bytesAt m a 4 := by
  simp only [bytesAt]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  exact Mem.extractLsb'_read m a hj

theorem writeW_readW (m m' : Mem) (D S : Addr) :
    m'.writeW D (m.readW S 32) = writeBytes m' D (bytesAt m S 4) := by
  rw [Mem.writeW, Mem.readW, show (32 / 8 : Nat) = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq,
    write_eq_writeBytes, read4_bytes]

theorem copyWords_ok (s : State) {S D : BitVec 32} {k : Nat} (h : WordsPre s S D k) :
    WP isa copyWords s fun s' => s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * k)) ∧
      s'.gpr .edi = S + BitVec.ofNat 32 (4 * k) ∧ s'.gpr .edx = D + BitVec.ofNat 32 (4 * k) ∧ Keeps s s' := by
  have hS := h.fitS
  have hD := h.fitD
  refine WP.loop (M := isa) (body := .block wordBody) (c := .ne)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .edi = S + BitVec.ofNat 32 (4 * i) ∧
      t.gpr .edx = D + BitVec.ofNat 32 (4 * i) ∧ t.gpr .ecx = BitVec.ofNat 32 (k - i) ∧
      t.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * i)) ∧ Keeps s t) ?_ (k - 0) _
    ⟨0, rfl, h.pos, by rw [h.edi]; simp, by rw [h.edx]; simp, by rw [h.ecx, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, edi, edx, ecx, mem, kp⟩
  have hin : 4 * i + 4 ≤ 4 * k := by omega_using [hi]
  have aS : w64 (S + BitVec.ofNat 32 (4 * i)) = w64 S + BitVec.ofNat 64 (4 * i) := w64_add (by omega_using [hS, hi])
  have aD : w64 (D + BitVec.ofNat 32 (4 * i)) = w64 D + BitVec.ofNat 64 (4 * i) := w64_add (by omega_using [hD, hi])
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 4 * k⟩] rs) : InRegions rs (P + BitVec.ofNat 64 (4 * i)) 4 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega_using [hS, hi])⟩
  obtain ⟨t', run', mem', edi', edx', ecx', zf', kp'⟩ := wordStep_ok t (w := k - i) edi edx ecx
    (by rw [kp.rd, kp.wr, aS]; exact cov _ _ h.rd) (by rw [kp.wr, aD]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hk32 : k < 2 ^ 32 := by omega_using [hS]
  have hmem : t'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * (i + 1))) := by
    rw [mem', mem, aS, aD, Mem.readW, read_kept h.disj hin (by omega_using [hS]), ← Mem.readW, writeW_readW,
      show 4 * (i + 1) = 4 * i + 4 by omega_using [], bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega_using [hS, hi]), Proof.Cmac.bytesAt_length]
  have hz : t'.zf = some (decide (i + 1 = k)) := by rw [zf', pred_beq hi hk32]
  by_cases he : i + 1 = k
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edi', he], by rw [edx', he], kp.trans kp'⟩
  · right
    refine ⟨by simp [eval, hz, he], k - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], edi', edx',
      by rw [ecx', pred_count hi hk32], hmem, kp.trans kp'⟩

theorem shr2 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [hn])]

theorem and3 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 3 < 2 ^ 32 by decide), Nat.mod_eq_of_lt (by omega_using []),
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_add_of_lt {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- A run keeps a register no instruction of the code writes. -/
theorem WP.keepGpr {c : Prog isa} {s : State} {Q : State → Prop} {r : Reg} (h : WP isa c s Q)
    (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p, n⟩] rs := by
  have := covers_off (d := 0) (n := n) h (by omega_using [hn]) hk
  rwa [BitVec.add_zero] at this

/-- What the copy of the slice that the descriptor at `A₀` lists needs: its
address `S` and length `n` there, `n` bytes at `S` to copy to `D`, apart, and
the descriptor apart from them. -/
structure SlicePre (s : State) (A₀ S D : BitVec 32) (n : Nat) : Prop where
  esi : s.gpr .esi = A₀
  edx : s.gpr .edx = D
  d0 : InRegions (s.rd ++ s.wr) (w64 A₀) 4
  d4 : InRegions (s.rd ++ s.wr) (w64 (A₀ + BitVec.ofNat 32 4)) 4
  w0 : s.mem.readW (w64 A₀) 32 = S
  w4 : s.mem.readW (w64 (A₀ + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 n
  lt : n < 2 ^ 32
  fitS : S.toNat + n ≤ 2 ^ 32
  fitD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨w64 S, n⟩] (s.rd ++ s.wr)
  wr : 0 < n → Covers [⟨w64 D, n⟩] s.wr
  disj : (⟨w64 S, n⟩ : Region).Disjoint ⟨w64 D, n⟩
  dd : (⟨w64 (A₀ + BitVec.ofNat 32 4), 4⟩ : Region).Disjoint ⟨w64 D, n⟩

section
variable {s : State} {A₀ S D : BitVec 32} {n : Nat}

/-- After `wordsArg`: the slice's address in `edi` and its number of whole
words in `ecx`. -/
structure Words1 (s : State) (A₀ S D : BitVec 32) (n : Nat) (s₁ : State) : Prop where
  esi : s₁.gpr .esi = A₀
  edi : s₁.gpr .edi = S
  edx : s₁.gpr .edx = D
  ecx : s₁.gpr .ecx = BitVec.ofNat 32 (n / 4)
  zf : s₁.zf = some (decide (n / 4 = 0))
  mem : s₁.mem = s.mem
  keep : Keeps s s₁

/-- After the whole words: `edi` and `edx` past them. -/
structure Words2 (s : State) (A₀ S D : BitVec 32) (n : Nat) (s₂ : State) : Prop where
  esi : s₂.gpr .esi = A₀
  edi : s₂.gpr .edi = S + BitVec.ofNat 32 (4 * (n / 4))
  edx : s₂.gpr .edx = D + BitVec.ofNat 32 (4 * (n / 4))
  mem : s₂.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * (n / 4)))
  keep : Keeps s s₂

/-- After `bytesArg`: the number of last bytes in `ecx`. -/
structure Bytes1 (s : State) (A₀ S D : BitVec 32) (n : Nat) (s₃ : State) : Prop extends Words2 s A₀ S D n s₃ where
  ecx : s₃.gpr .ecx = BitVec.ofNat 32 (n % 4)
  zf : s₃.zf = some (decide (n % 4 = 0))

theorem wordsArg_wp (h : SlicePre s A₀ S D n) : WP isa (.block wordsArg) s (Words1 s A₀ S D n) := by
  have hn := h.lt
  refine WP.of_runBlock ⟨_, by xrun [wordsArg, add_zero32, h.esi, h.d0, h.d4], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ⟨fun r hr => ?_, rfl, rfl⟩⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_false, reduceCtorEq, h.esi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.w0]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_false, reduceCtorEq, h.edx]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq, h.w4,
      shr2 hn]
  · simp only [zf_arithFlags, gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, ite_false, reduceCtorEq,
      h.w4, shr2 hn, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero (show n / 4 < 2 ^ 32 by omega_using [hn])]
  · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
    simp [gpr_setMem, gpr_setReg, gpr_arithFlags, gpr_setFlags, h₁, h₂, h₃, h₄]

theorem words_wp (h : SlicePre s A₀ S D n) {s₁ : State} (h₁ : Words1 s A₀ S D n s₁) :
    WP isa (.ite .e (.block []) copyWords) s₁ (Words2 s A₀ S D n) := by
  have hn := h.lt
  have hfS := h.fitS
  have hfD := h.fitD
  refine WP.ite (decide (n / 4 = 0)) h₁.zf (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 4 = 0 := by simpa using ht
    refine WP.block_nil ⟨h₁.esi, ?_, ?_, ?_, h₁.keep⟩
    · rw [h₁.edi, h0]; simp
    · rw [h₁.edx, h0]; simp
    · rw [h₁.mem, h0, Nat.mul_zero]; simp [bytesAt, writeBytes_nil]
  · have h0 : n / 4 ≠ 0 := by simpa using hf
    have hw : WordsPre s₁ S D (n / 4) :=
      ⟨h₁.edi, h₁.edx, h₁.ecx, by omega_using [h0], by omega_using [hfS], by omega_using [hfD],
        by rw [h₁.keep.rd, h₁.keep.wr]; exact covers_prefix h.rd (by omega_using []) (by omega_using [hn]),
        by rw [h₁.keep.wr]; exact covers_prefix (h.wr (by omega_using [h0])) (by omega_using []) (by omega_using [hn]),
        (h.disj.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Region.sub_prefix (by omega_using []))⟩
    refine WP.mono (WP.keepGpr (r := .esi) (copyWords_ok s₁ hw) (by decide))
      fun s₂ ⟨⟨m₂, edi₂, edx₂, kp₂⟩, esi₂⟩ => ⟨by rw [esi₂, h₁.esi], edi₂, edx₂, by rw [m₂, h₁.mem],
        h₁.keep.trans kp₂⟩

theorem frame_words {s₂ : State} (h₂ : Words2 s A₀ S D n s₂) : Frame [⟨w64 D, n⟩] s.mem s₂.mem := by
  have hlen : (bytesAt s.mem (w64 S) (4 * (n / 4))).length = 4 * (n / 4) := Proof.Cmac.bytesAt_length _ _ _
  rw [h₂.mem]
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
  omega_using []

theorem bytesArg_wp (h : SlicePre s A₀ S D n) {s₂ : State} (h₂ : Words2 s A₀ S D n s₂) :
    WP isa (.block bytesArg) s₂ (Bytes1 s A₀ S D n) := by
  have hn := h.lt
  have w4₂ : s₂.mem.readW (w64 (A₀ + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 n := by
    rw [(frame_words h₂).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.dd) (by decide), h.w4]
  have d4 : InRegions (s₂.rd ++ s₂.wr) (w64 (A₀ + BitVec.ofNat 32 4)) 4 := by
    rw [h₂.keep.rd, h₂.keep.wr]; exact h.d4
  refine WP.of_runBlock ⟨_, by xrun [bytesArg, h₂.esi, d4], ?_⟩
  refine ⟨⟨?_, ?_, ?_, ?_, h₂.keep.trans ⟨fun r hr => ?_, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq, h₂.esi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq, h₂.edi]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_false, reduceCtorEq, h₂.edx]
  · simp only [mem_setReg, mem_arithFlags, h₂.mem]
  · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
    simp [gpr_setMem, gpr_setReg, gpr_arithFlags, h₁, h₂, h₃, h₄]
  · simp only [gpr_setMem, gpr_setReg, gpr_arithFlags, ite_true, w4₂, and3 hn]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, ite_true, w4₂, and3 hn,
      VG.X86.Wp.ofNat_beq_zero (show n % 4 < 2 ^ 32 by omega_using [])]

theorem bytes_wp (h : SlicePre s A₀ S D n) {s₃ : State} (h₃ : Bytes1 s A₀ S D n s₃) :
    WP isa (.ite .e (.block []) copyLoop) s₃ fun s' =>
      s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n) ∧
      s'.gpr .edx = D + BitVec.ofNat 32 n ∧ Keeps s s' := by
  have hn := h.lt
  have hfS := h.fitS
  have hfD := h.fitD
  have hqr : 4 * (n / 4) + n % 4 = n := by omega_using []
  have hlen : (bytesAt s.mem (w64 S) (4 * (n / 4))).length = 4 * (n / 4) := Proof.Cmac.bytesAt_length _ _ _
  have hfr := frame_words h₃.toWords2
  have hS : (⟨w64 S + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨w64 S, n⟩ :=
    Offset.sub_base _ (by omega_using [])
  have hD : (⟨w64 D + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨w64 D, n⟩ :=
    Offset.sub_base _ (by omega_using [])
  have hrest : bytesAt s₃.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) =
      bytesAt s.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) := by
    refine Proof.Cmac.bytesAt_frame hfr (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_singleton] at hr; subst hr
    exact h.disj.sub_left hS
  have hend : D + BitVec.ofNat 32 (4 * (n / 4)) + BitVec.ofNat 32 (n % 4) = D + BitVec.ofNat 32 n := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hqr]
  have hall : writeBytes (writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * (n / 4))))
      (w64 D + BitVec.ofNat 64 (4 * (n / 4)))
      (bytesAt s.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4)) =
      writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n) := by
    have e := writeBytes_append s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * (n / 4)))
      (bytesAt s.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4))
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega_using [hn])
    rw [hlen] at e
    rw [e, ← bytesAt_append, hqr]
  refine WP.ite (decide (n % 4 = 0)) h₃.zf (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 4 = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, ?_, h₃.keep⟩
    · rw [h₃.mem, ← hall, h0]; simp [bytesAt, writeBytes_nil]
    · rw [h₃.edx, ← hend, h0]; simp
  · have h0 : n % 4 ≠ 0 := by simpa using hf
    have aS : w64 (S + BitVec.ofNat 32 (4 * (n / 4))) = w64 S + BitVec.ofNat 64 (4 * (n / 4)) :=
      w64_add (by omega_using [hfS, h0])
    have aD : w64 (D + BitVec.ofNat 32 (4 * (n / 4))) = w64 D + BitVec.ofNat 64 (4 * (n / 4)) :=
      w64_add (by omega_using [hfD, h0])
    have lp : LoopPre s₃ (S + BitVec.ofNat 32 (4 * (n / 4))) (D + BitVec.ofNat 32 (4 * (n / 4))) (n % 4) :=
      ⟨h₃.edi, h₃.edx, h₃.ecx, by omega_using [h0], by omega_using [],
        by rw [toNat_add_of_lt (by omega_using [hfS, h0])]; omega_using [hfS], by rw [toNat_add_of_lt (by omega_using [hfD, h0])]; omega_using [hfD],
        by rw [h₃.keep.rd, h₃.keep.wr, aS]; exact covers_off h.rd (by omega_using []) (by omega_using [hn]),
        by rw [h₃.keep.wr, aD]; exact covers_off (h.wr (by omega_using [h0])) (by omega_using []) (by omega_using [hn]),
        by rw [aS, aD]; exact (h.disj.sub_left hS).sub_right hD⟩
    refine WP.mono (copyLoop_ok s₃ lp) fun s₄ c => ⟨?_, by rw [c.edx, hend],
      h₃.keep.trans ⟨fun r hr => ?_, c.rd, c.wr⟩⟩
    · rw [c.mem, aS, aD, hrest, h₃.mem, hall]
    · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
      exact c.other r h₁ h₄ h₃ h₂

/-- `copySlice`: the `n` bytes at `S` to `D`, and `edx` past them. -/
theorem copySlice_wp (s : State) (h : SlicePre s A₀ S D n) :
    WP isa copySlice s fun s' => s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n) ∧
      s'.gpr .edx = D + BitVec.ofNat 32 n ∧ Keeps s s' :=
  WP.seq (WP.mono (wordsArg_wp h) fun _ h₁ => WP.seq (WP.mono (words_wp h h₁) fun _ h₂ =>
    WP.seq (WP.mono (bytesArg_wp h h₂) fun _ h₃ => bytes_wp h h₃)))

end

end VG.Proof.AesGcm.X86.Gather

end

end


/-!
# AES-GCM one-shot encryption out of place, from a list of slices, x86: gathering the slices

Untrusted: everything here is checked by Lean. `gather` copies the `cnt`
slices that the descriptors at `esi` list, one after the other, to `edx`
(`gather_wp`): with `i` of them copied (`GInv`), `esi` is at descriptor `i`,
`ebx` holds `cnt - i`, `edx` is `gatheredLen` of the first `i` past `dst`, and
the memory is the one on entry with their concatenation (`gathered`) written
at `dst`. The descriptors and the slices are apart from `dst`, so they are
what they were on entry. Descriptor `i` is at `Src + 8i`: the slice's address
(`sb`), then its length (`sl`). A function gathering the slices runs in a
frame of stack of its own (`WP.alloc`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86.Gather

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesGcm.X86 VG.Impl.AesGcm.X86.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (gathered gatheredLen)

/-- The registers the gathering writes. -/
abbrev gatherRegs : List Reg := [.eax, .ebx, .ecx, .edx, .esi, .edi]

/-- What the gathering keeps: the other registers and the permissions. -/
structure GKeeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ gatherRegs → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem GKeeps.refl (s : State) : GKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem GKeeps.trans {s t u : State} (h₁ : GKeeps s t) (h₂ : GKeeps t u) : GKeeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Keeps.gkeeps {s t : State} (h : Keeps s t) : GKeeps s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (by
    simp only [copyRegs, gatherRegs, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with e | e | e | e <;> simp [e])), h.rd, h.wr⟩

theorem add_ofNat_zero {w : Nat} (x : BitVec w) : x + BitVec.ofNat w 0 = x := BitVec.add_zero x

section
variable (m : Mem) (Src : BitVec 32)

/-- Slice `i`: its address and its length, from its descriptor at `Src + 8i`. -/
abbrev sb (i : Nat) : BitVec 32 := m.readW (w64 (Src + BitVec.ofNat 32 (8 * i))) 32
abbrev sl (i : Nat) : Nat := (m.readW (w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4)) 32).toNat

end

/-- Descriptor `i`'s words, from the 32-bit pointer to the descriptors. -/
theorem descA {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) (d : Nat)
    (hd : d < 8) :
    w64 Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) + BitVec.ofNat 64 d =
      w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 d) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show i * (2 * (32 / 8)) + d = 8 * i + d by omega_using [], w64_add (by omega_using [hdw, hi, hd])]

theorem descA0 {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    w64 Src + BitVec.ofNat 64 (i * (2 * (32 / 8))) = w64 (Src + BitVec.ofNat 32 (8 * i)) := by
  have := descA hdw hi 0 (by decide)
  rwa [add_ofNat_zero, add_ofNat_zero] at this

theorem gl_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gatheredLen 32 m (w64 Src) (i + 1) = gatheredLen 32 m (w64 Src) i + sl m Src i := by
  rw [Proof.Gcm.gatheredLen_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide)]

theorem pt_succ {m : Mem} {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    gathered 32 m (w64 Src) (i + 1) =
      gathered 32 m (w64 Src) i ++ bytesAt m (w64 (sb m Src i)) (sl m Src i) := by
  rw [Proof.Gcm.gathered_succ, show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]

theorem gl_mono (m : Mem) (Src : BitVec 32) {cnt i j : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (h : i ≤ j)
    (hj : j ≤ cnt) : gatheredLen 32 m (w64 Src) i ≤ gatheredLen 32 m (w64 Src) j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h
    · exact Nat.le_refl _
    · rw [gl_succ hdw (by omega_using [hj])]; exact Nat.le_trans (ih (by omega_using [h]) (by omega_using [hj])) (Nat.le_add_right _ _)

/-- Slice `i` is listed. -/
theorem slice_mem (m : Mem) {Src : BitVec 32} {cnt i : Nat} (hdw : Src.toNat + cnt * 8 ≤ 2 ^ 32) (hi : i < cnt) :
    (⟨w64 (sb m Src i), sl m Src i⟩ : Region) ∈ Sig.listed 32 m .u8 (w64 Src) cnt := by
  simp only [Sig.listed, List.mem_map, List.mem_range]
  refine ⟨i, hi, ?_⟩
  rw [show (32 / 8 : Nat) = 4 from rfl, descA hdw hi 4 (by decide), descA0 hdw hi]
  simp only [Elem.size, Nat.mul_one]

/-- What the gathering needs: `cnt` descriptors at `Src`, listing slices of
`L` bytes in all, to copy to `Dst`, apart from them. -/
structure GatherPre (t : State) (Src Dst : BitVec 32) (cnt L : Nat) : Prop where
  esi : t.gpr .esi = Src
  ebx : t.gpr .ebx = BitVec.ofNat 32 cnt
  edx : t.gpr .edx = Dst
  hcnt : cnt < 2 ^ 32
  dw : Src.toNat + cnt * 8 ≤ 2 ^ 32
  fitD : Dst.toNat + L ≤ 2 ^ 32
  len : gatheredLen 32 t.mem (w64 Src) cnt = L
  dsr : Covers [⟨w64 Src, cnt * 8⟩] (t.rd ++ t.wr)
  lsr : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, Covers [r] (t.rd ++ t.wr)
  lfit : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, r.base.toNat + r.len ≤ 2 ^ 32
  dw' : Covers [⟨w64 Dst, L⟩] t.wr
  dsd : (⟨w64 Src, cnt * 8⟩ : Region).Disjoint ⟨w64 Dst, L⟩
  lsd : ∀ r ∈ Sig.listed 32 t.mem .u8 (w64 Src) cnt, r.Disjoint ⟨w64 Dst, L⟩

/-- The loop's invariant: the first `i` slices copied. -/
structure GInv (t u : State) (Src Dst : BitVec 32) (cnt i : Nat) : Prop where
  esi : u.gpr .esi = Src + BitVec.ofNat 32 (8 * i)
  ebx : u.gpr .ebx = BitVec.ofNat 32 (cnt - i)
  edx : u.gpr .edx = Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)
  mem : u.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) i)
  keep : GKeeps t u

theorem GInv.init {t : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    GInv t t Src Dst cnt 0 :=
  ⟨by rw [h.esi]; simp, by rw [h.ebx, Nat.sub_zero], by rw [h.edx]; simp [gatheredLen, Sig.listed],
    by simp [gathered, Sig.listed, writeBytes_nil], GKeeps.refl t⟩

theorem next_ok (u : State) {A₀ : BitVec 32} {w : Nat} (h0 : u.gpr .esi = A₀) (hlr : u.gpr .ebx = BitVec.ofNat 32 w) :
    ∃ u', runBlock isa next u = some u' ∧ u'.gpr .esi = A₀ + BitVec.ofNat 32 8 ∧
      u'.gpr .ebx = BitVec.ofNat 32 w - BitVec.ofNat 32 1 ∧ u'.zf = some (BitVec.ofNat 32 w - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .esi → r ≠ .ebx → u'.gpr r = u.gpr r) ∧ u'.mem = u.mem ∧ u'.rd = u.rd ∧ u'.wr = u.wr := by
  refine ⟨_, by xrun [next, h0, hlr], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h0]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, hlr]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hlr]
  · simp [gpr_setReg, gpr_arithFlags, h₁, h₂]
  all_goals rfl

section
variable {t u : State} {Src Dst : BitVec 32} {cnt L i : Nat} (h : GatherPre t Src Dst cnt L)
include h

theorem gl_le (hi : i ≤ cnt) : gatheredLen 32 t.mem (w64 Src) i ≤ L :=
  h.len ▸ gl_mono t.mem Src h.dw hi (Nat.le_refl _)

/-- What the copy of slice `i` needs, with `i` copied. -/
theorem slicePre_of (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    SlicePre u (Src + BitVec.ofNat 32 (8 * i)) (sb t.mem Src i)
      (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) (sl t.mem Src i) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (w64 Src) (i + 1) ≤ L := gl_le h (by omega_using [hi])
  have hlen : (gathered 32 t.mem (w64 Src) i).length = gatheredLen 32 t.mem (w64 Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨w64 Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega_using [hgl]
  -- The descriptor.
  have a0 : w64 (Src + BitVec.ofNat 32 (8 * i)) = w64 Src + BitVec.ofNat 64 (8 * i) :=
    w64_add (by omega_using [hi, hdw])
  have a4 : w64 (Src + BitVec.ofNat 32 (8 * i) + BitVec.ofNat 32 4) =
      w64 Src + BitVec.ofNat 64 (8 * i + 4) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, w64_add (by omega_using [hi, hdw])]
  have din (d : Nat) (hd : d + 4 ≤ cnt * 8) : InRegions (u.rd ++ u.wr) (w64 Src + BitVec.ofNat 64 d) 4 := by
    rw [hu.keep.rd, hu.keep.wr]; exact h.dsr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ hd (by omega_using [hc, hd])⟩
  have dsub (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      Region.Sub ⟨w64 Src + BitVec.ofNat 64 d, 4⟩ ⟨w64 Src, cnt * 8⟩ := Offset.sub_base _ hd
  have dkeep (d : Nat) (hd : d + 4 ≤ cnt * 8) :
      u.mem.readW (w64 Src + BitVec.ofNat 64 d) 32 = t.mem.readW (w64 Src + BitVec.ofNat 64 d) 32 :=
    hfr.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.dsd.sub_left (dsub d hd)) (by decide)
  -- The slice.
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨w64 (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨w64 Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  -- Where the slice goes: past the first `i`, unless it is empty (and may then be at the end of the
  -- address space, where `r2` wraps).
  have aD (hp : 0 < sl t.mem Src i) : w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) =
      w64 Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (w64 Src) i) := w64_add (by omega_using [hfD, hgl, hp])
  have hsub : (⟨w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)), sl t.mem Src i⟩ :
      Region).Sub ⟨w64 Dst, L⟩ := by
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp]; exact Offset.sub_base _ hgl
    · intro x hx; simp only [Region.Contains] at hx; omega
  exact
    { esi := hu.esi
      edx := hu.edx
      d0 := by rw [a0]; exact din _ (by omega_using [hi])
      d4 := by rw [a4]; exact din _ (by omega_using [hi])
      w0 := by rw [a0, dkeep _ (by omega_using [hi]), ← a0]
      w4 := by rw [a4, dkeep _ (by omega_using [hi]), ← a4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      lt := by simp only [sl]; exact BitVec.isLt _
      fitS := by have := hfit; simp only at this; rwa [toNat_w64] at this
      fitD := by
        by_cases hp : 0 < sl t.mem Src i
        · rw [toNat_add_of_lt (by omega_using [hfD, hgl, hp])]; omega_using [hfD, hgl]
        · have := (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)).isLt; omega_using [hp]
      rd := by rw [hu.keep.rd, hu.keep.wr]; exact h.lsr _ hmem
      wr := fun hp => by
        rw [hu.keep.wr, aD hp]
        exact covers_off h.dw' hgl (by omega_using [hfD])
      disj := hsd.sub_right hsub
      dd := by
        rw [a4]
        exact (h.dsd.sub_left (dsub _ (by omega_using [hi]))).sub_right hsub }

/-- One iteration: slice `i` copied, `r0` at the next descriptor and `lr`
decremented. -/
theorem body_wp (hi : i < cnt) (hu : GInv t u Src Dst cnt i) :
    WP isa (.seq copySlice (.block next)) u fun u' => GInv t u' Src Dst cnt (i + 1) ∧
      u'.zf = some (decide (i + 1 = cnt)) := by
  have hc := h.hcnt
  have hdw := h.dw
  have hfD := h.fitD
  have hgl : gatheredLen 32 t.mem (w64 Src) (i + 1) ≤ L := gl_le h (by omega_using [hi])
  have hlen : (gathered 32 t.mem (w64 Src) i).length = gatheredLen 32 t.mem (w64 Src) i :=
    Proof.Gcm.length_gathered _ _ _ _
  rw [gl_succ hdw hi] at hgl
  have hfr : Frame [⟨w64 Dst, L⟩] t.mem u.mem := by
    rw [hu.mem]
    refine writeBytes_frame t.mem _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega_using [hgl]
  have hmem := slice_mem t.mem hdw hi
  have hsd : (⟨w64 (sb t.mem Src i), sl t.mem Src i⟩ : Region).Disjoint ⟨w64 Dst, L⟩ := h.lsd _ hmem
  have hfit := h.lfit _ hmem
  have aD (hp : 0 < sl t.mem Src i) : w64 (Dst + BitVec.ofNat 32 (gatheredLen 32 t.mem (w64 Src) i)) =
      w64 Dst + BitVec.ofNat 64 (gatheredLen 32 t.mem (w64 Src) i) := w64_add (by omega_using [hfD, hgl, hp])
  have hsp := slicePre_of h hi hu
  refine WP.seq (WP.mono (copySlice_wp u hsp) fun u₂ ⟨m₂, r2₂, kp₂⟩ => ?_)
  obtain ⟨u₃, run₃, r0₃, lr₃, z₃, g₃, m₃, rd₃, wr₃⟩ :=
    next_ok u₂ (w := cnt - i) (by rw [kp₂.gpr _ (by decide), hu.esi]) (by rw [kp₂.gpr _ (by decide), hu.ebx])
  refine WP.of_runBlock ⟨u₃, run₃, ?_⟩
  -- The slice's bytes were what they were on entry.
  have hbytes : bytesAt u.mem (w64 (sb t.mem Src i)) (sl t.mem Src i) =
      bytesAt t.mem (w64 (sb t.mem Src i)) (sl t.mem Src i) := by
    refine Proof.Cmac.bytesAt_frame hfr (fun r hr => ?_) (by omega_using [hfD, hgl])
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd
  refine ⟨⟨?_, ?_, ?_, ?_, hu.keep.trans (kp₂.gkeeps.trans
    ⟨fun r hr => g₃ r (by intro e; subst e; simp [gatherRegs] at hr) (by intro e; subst e; simp [gatherRegs] at hr),
      rd₃, wr₃⟩)⟩, ?_⟩
  · rw [r0₃, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  · rw [lr₃, pred_count hi hc]
  · rw [g₃ _ (by decide) (by decide), r2₂, BitVec.add_assoc, BitVec.ofNat_add_ofNat, ← gl_succ hdw hi]
  · rw [m₃, m₂, hbytes, hu.mem, pt_succ hdw hi]
    by_cases hp : 0 < sl t.mem Src i
    · rw [aD hp, ← hlen, writeBytes_append _ _ _ _ (by rw [hlen, Proof.Cmac.bytesAt_length]; omega_using [hfD, hgl])]
    · have h0 : sl t.mem Src i = 0 := by omega_using [hp]
      rw [h0]; simp [bytesAt, writeBytes_nil]
  · rw [z₃, pred_beq hi hc]

end

/-- `gatherLoop`: the `cnt ≥ 1` slices copied to `Dst`. -/
theorem gatherLoop_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hpos : 1 ≤ cnt) :
    WP isa gatherLoop t fun t' =>
      t'.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) cnt) ∧ GKeeps t t' := by
  refine WP.loop (M := isa) (c := .ne)
    (fun (w : Nat) (u : State) => ∃ i, w = cnt - i ∧ i < cnt ∧ GInv t u Src Dst cnt i) ?_ (cnt - 0) _
    ⟨0, rfl, hpos, GInv.init h⟩
  rintro w u ⟨i, rfl, hi, hu⟩
  refine WP.mono (body_wp h hi hu) fun u₃ ⟨h₃, z₃⟩ => ?_
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = cnt) := by
    show u₃.zf.map (!·) = _; rw [z₃]; rfl
  by_cases he : i + 1 = cnt
  · left
    exact ⟨by rw [ev]; simp [he], by rw [h₃.mem, he], h₃.keep⟩
  · right
    exact ⟨by rw [ev]; simp [he], cnt - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, he], h₃⟩

/-- `GatherPre` in a state with the same registers, memory and permissions. -/
theorem GatherPre.of_eq {t t' : State} {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L)
    (hg : t'.gpr = t.gpr) (hm : t'.mem = t.mem) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) :
    GatherPre t' Src Dst cnt L := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩ := h
  exact ⟨by rw [hg]; exact a₁, by rw [hg]; exact a₂, by rw [hg]; exact a₃, a₄, a₅, a₆, by rw [hm]; exact a₇,
    by rw [hrd, hwr]; exact a₈, by rw [hm, hrd, hwr]; exact a₉, by rw [hm]; exact a₁₀, by rw [hwr]; exact a₁₁, a₁₂,
    by rw [hm]; exact a₁₃⟩

/-- `cmp ebx, 0`: only the flags change. -/
theorem cmp_ok (t : State) {cnt : Nat} (hb : t.gpr .ebx = BitVec.ofNat 32 cnt) (hc : cnt < 2 ^ 32) :
    ∃ t₁, runBlock isa [.alu .cmp .ebx (imm 0)] t = some t₁ ∧ t₁.zf = some (decide (cnt = 0)) ∧
      t₁.gpr = t.gpr ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
  refine ⟨_, by xrun [], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [zf_arithFlags, hb, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero hc]
  all_goals rfl

/-- `gather`: the `cnt` slices copied to `Dst`. -/
theorem gather_wp (t : State) {Src Dst : BitVec 32} {cnt L : Nat} (h : GatherPre t Src Dst cnt L) :
    WP isa gather t fun t' =>
      t'.mem = writeBytes t.mem (w64 Dst) (gathered 32 t.mem (w64 Src) cnt) ∧ GKeeps t t' := by
  obtain ⟨t₁, run₁, z₁, g₁, m₁, rd₁, wr₁⟩ := cmp_ok t h.ebx h.hcnt
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite (decide (cnt = 0)) z₁ (fun ht => ?_) (fun hf => ?_)
  · have h0 : cnt = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨by rw [m₁]; simp [gathered, Sig.listed, writeBytes_nil],
      ⟨fun r _ => by rw [g₁], rd₁, wr₁⟩⟩
  · have h0 : cnt ≠ 0 := by simpa using hf
    refine WP.mono (gatherLoop_wp t₁ (h.of_eq g₁ m₁ rd₁ wr₁) (by omega_using [h0])) fun t' ⟨m, k⟩ => ⟨?_, ?_⟩
    · rw [m, m₁]
    · exact ⟨fun r hr => by rw [k.gpr r hr, g₁], k.rd.trans rd₁, k.wr.trans wr₁⟩

/-! ## A frame of stack -/

/-- The state after reserving `bytes` bytes of stack. -/
def allocated (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp - BitVec.ofNat 32 bytes) with
    wr := ⟨w64 (s.gpr .esp - BitVec.ofNat 32 bytes), bytes⟩ :: s.wr }

/-- The state after releasing them. -/
def freed (bytes : Nat) (s : State) : State :=
  { s.setReg .esp (s.gpr .esp + BitVec.ofNat 32 bytes) with wr := s.wr.tail }

/-- A frame of `bytes` bytes of stack around a body that never writes `esp`:
the postcondition holds whatever the frame's bytes and the unknowns are after
the release. -/
theorem WP.alloc {bytes : Nat} {body : Prog isa} {s : State} {Q : State → Prop}
    (hn : 0 < bytes ∧ bytes < 4096 ∧ bytes % 4 = 0) (hsp : bytes ≤ (s.gpr .esp).toNat) (hb : NoSp body)
    (h : WP isa body (allocated bytes s) fun s₂ => ∀ m u,
      Frame [below (s.gpr .esp) bytes] s₂.mem m → Q { freed bytes s₂ with mem := m, unknowns := u }) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨t, s₂, he, hq⟩ := h
  obtain ⟨-, hw⟩ := Exec.rdwr he
  have hp := Exec.gpr hb he
  have ha : isa.push (.alloc bytes) s = some (allocated bytes s) := by
    simp only [isa, push, hn.1, hn.2.1, hn.2.2, hsp, and_self, ite_true]
    rfl
  have hf : isa.pop (.free bytes) (allocated bytes s) s₂ = some { freed bytes s₂ with
      mem := lose s₂.mem ((s₂.gpr .esp).setWidth 64) bytes s₂.unknowns
      unknowns := fun n => s₂.unknowns (n + bytes / 2) } := by
    simp only [isa, pop]
    refine ite_eq_left ⟨hn.1, hn.2.1, hn.2.2, hp, hw, ?_⟩
    rfl
  have e : (s₂.gpr .esp).setWidth 64 = (below (s.gpr .esp) bytes).base := by
    rw [hp]; simp [allocated, gpr_setReg, below]
  exact ⟨_, _, Exec.frame ha he hf, hq _ _ (by rw [e]; exact lose_frame _ _ _ _)⟩

@[simp] theorem allocated_esp (n : Nat) (s : State) : (allocated n s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 n := by
  simp [allocated, gpr_setReg]
theorem allocated_gpr (n : Nat) (s : State) {r : Reg} (h : r ≠ .esp) : (allocated n s).gpr r = s.gpr r := by
  simp [allocated, gpr_setReg, h]
@[simp] theorem allocated_mem (n : Nat) (s : State) : (allocated n s).mem = s.mem := rfl
@[simp] theorem allocated_rd (n : Nat) (s : State) : (allocated n s).rd = s.rd := rfl
@[simp] theorem allocated_wr (n : Nat) (s : State) :
    (allocated n s).wr = ⟨w64 (s.gpr .esp - BitVec.ofNat 32 n), n⟩ :: s.wr := rfl

end VG.Proof.AesGcm.X86.Gather
