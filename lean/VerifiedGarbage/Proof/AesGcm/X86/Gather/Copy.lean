import VerifiedGarbage.Proof.AesGcm.X86.Gather.Callee
import VerifiedGarbage.Proof.AesGcm.X86.Loops
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Cmac.Frame

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
  exact hd _ (Offset.contains_base S (show j + k + 1 ≤ L by omega) (by omega))
    (Region.sub_prefix (show j ≤ L by omega) _ hcon)

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
  have hin : 4 * i + 4 ≤ 4 * k := by omega
  have aS : w64 (S + BitVec.ofNat 32 (4 * i)) = w64 S + BitVec.ofNat 64 (4 * i) := w64_add (by omega)
  have aD : w64 (D + BitVec.ofNat 32 (4 * i)) = w64 D + BitVec.ofNat 64 (4 * i) := w64_add (by omega)
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 4 * k⟩] rs) : InRegions rs (P + BitVec.ofNat 64 (4 * i)) 4 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega)⟩
  obtain ⟨t', run', mem', edi', edx', ecx', zf', kp'⟩ := wordStep_ok t (w := k - i) edi edx ecx
    (by rw [kp.rd, kp.wr, aS]; exact cov _ _ h.rd) (by rw [kp.wr, aD]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hk32 : k < 2 ^ 32 := by omega
  have hmem : t'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) (4 * (i + 1))) := by
    rw [mem', mem, aS, aD, Mem.readW, read_kept h.disj hin (by omega), ← Mem.readW, writeW_readW,
      show 4 * (i + 1) = 4 * i + 4 by omega, bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), Proof.Cmac.bytesAt_length]
  have hz : t'.zf = some (decide (i + 1 = k)) := by rw [zf', pred_beq hi hk32]
  by_cases he : i + 1 = k
  · left
    refine ⟨by simp [eval, hz, he], by rw [hmem, he], by rw [edi', he], by rw [edx', he], kp.trans kp'⟩
  · right
    refine ⟨by simp [eval, hz, he], k - (i + 1), by omega, i + 1, rfl, by omega, edi', edx',
      by rw [ecx', pred_count hi hk32], hmem, kp.trans kp'⟩

theorem shr2 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem and3 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 3 < 2 ^ 32 by decide), Nat.mod_eq_of_lt (by omega),
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_add_of_lt {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-- A run keeps a register no instruction of the code writes. -/
theorem WP.keepGpr {c : Prog isa} {s : State} {Q : State → Prop} {r : Reg} (h : WP isa c s Q)
    (hc : ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p, n⟩] rs := by
  have := covers_off (d := 0) (n := n) h (by omega) hk
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
      h.w4, shr2 hn, BitVec.sub_zero, VG.X86.Wp.ofNat_beq_zero (show n / 4 < 2 ^ 32 by omega)]
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
      ⟨h₁.edi, h₁.edx, h₁.ecx, by omega, by omega, by omega,
        by rw [h₁.keep.rd, h₁.keep.wr]; exact covers_prefix h.rd (by omega) (by omega),
        by rw [h₁.keep.wr]; exact covers_prefix (h.wr (by omega)) (by omega) (by omega),
        (h.disj.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))⟩
    refine WP.mono (WP.keepGpr (r := .esi) (copyWords_ok s₁ hw) (by decide))
      fun s₂ ⟨⟨m₂, edi₂, edx₂, kp₂⟩, esi₂⟩ => ⟨by rw [esi₂, h₁.esi], edi₂, edx₂, by rw [m₂, h₁.mem],
        h₁.keep.trans kp₂⟩

theorem frame_words {s₂ : State} (h₂ : Words2 s A₀ S D n s₂) : Frame [⟨w64 D, n⟩] s.mem s₂.mem := by
  have hlen : (bytesAt s.mem (w64 S) (4 * (n / 4))).length = 4 * (n / 4) := Proof.Cmac.bytesAt_length _ _ _
  rw [h₂.mem]
  refine writeBytes_frame _ _ _ ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
  omega

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
      VG.X86.Wp.ofNat_beq_zero (show n % 4 < 2 ^ 32 by omega)]

theorem bytes_wp (h : SlicePre s A₀ S D n) {s₃ : State} (h₃ : Bytes1 s A₀ S D n s₃) :
    WP isa (.ite .e (.block []) copyLoop) s₃ fun s' =>
      s'.mem = writeBytes s.mem (w64 D) (bytesAt s.mem (w64 S) n) ∧
      s'.gpr .edx = D + BitVec.ofNat 32 n ∧ Keeps s s' := by
  have hn := h.lt
  have hfS := h.fitS
  have hfD := h.fitD
  have hqr : 4 * (n / 4) + n % 4 = n := by omega
  have hlen : (bytesAt s.mem (w64 S) (4 * (n / 4))).length = 4 * (n / 4) := Proof.Cmac.bytesAt_length _ _ _
  have hfr := frame_words h₃.toWords2
  have hS : (⟨w64 S + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨w64 S, n⟩ :=
    Offset.sub_base _ (by omega)
  have hD : (⟨w64 D + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨w64 D, n⟩ :=
    Offset.sub_base _ (by omega)
  have hrest : bytesAt s₃.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) =
      bytesAt s.mem (w64 S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) := by
    refine Proof.Cmac.bytesAt_frame hfr (fun r hr => ?_) (by omega)
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
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)
    rw [hlen] at e
    rw [e, ← bytesAt_append, hqr]
  refine WP.ite (decide (n % 4 = 0)) h₃.zf (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 4 = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, ?_, h₃.keep⟩
    · rw [h₃.mem, ← hall, h0]; simp [bytesAt, writeBytes_nil]
    · rw [h₃.edx, ← hend, h0]; simp
  · have h0 : n % 4 ≠ 0 := by simpa using hf
    have aS : w64 (S + BitVec.ofNat 32 (4 * (n / 4))) = w64 S + BitVec.ofNat 64 (4 * (n / 4)) :=
      w64_add (by omega)
    have aD : w64 (D + BitVec.ofNat 32 (4 * (n / 4))) = w64 D + BitVec.ofNat 64 (4 * (n / 4)) :=
      w64_add (by omega)
    have lp : LoopPre s₃ (S + BitVec.ofNat 32 (4 * (n / 4))) (D + BitVec.ofNat 32 (4 * (n / 4))) (n % 4) :=
      ⟨h₃.edi, h₃.edx, h₃.ecx, by omega, by omega,
        by rw [toNat_add_of_lt (by omega)]; omega, by rw [toNat_add_of_lt (by omega)]; omega,
        by rw [h₃.keep.rd, h₃.keep.wr, aS]; exact covers_off h.rd (by omega) (by omega),
        by rw [h₃.keep.wr, aD]; exact covers_off (h.wr (by omega)) (by omega) (by omega),
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
