import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Impl.AesGcm.Arm.SealGather
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# AES-GCM one-shot encryption out of place, from a list of slices, ARMv7: copying a slice

Untrusted: everything here is checked by Lean. `copyWords` copies `k ≥ 1`
words from `r1` to `r2`, a word at a time through `r12`, counting `r3`
down (`copyWords_ok`); with `copyLoop` for the last bytes (`copyLoop_ok`),
`copySlice` copies the slice that the descriptor at `r0` lists to `r2`,
leaving `r2` past it (`copySlice_wp`). The bytes copied and the bytes written
do not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.Arm.Gather

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesGcm.Arm VG.Impl.AesGcm.Arm.SealGather VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Cmac.Stream (bytesAt_append)
open VG.Proof.AesGcm.Arm (LoopPre LoopOut copyLoop_ok addr_i dec32 z_dec eval_eq' eval_ne' z_cmp0 in_of_covers
  add_ofNat_zero add32_ofNat_assoc covers_prefix covers_off)

/-- The registers the copy of a slice writes. -/
abbrev copyRegs : List Reg := [.r1, .r2, .r3, .r12]

/-- What the copy of a slice keeps: the other registers, the stack pointer
and the permissions. -/
structure Keeps (s t : State) : Prop where
  gpr : ∀ r, r ∉ copyRegs → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h₁ : Keeps s t) (h₂ : Keeps t u) : Keeps s u :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

abbrev wordBody : List Instr :=
  [.ldr .r12 .r1 0, .str .r12 .r2 0, addI .r1 .r1 4, addI .r2 .r2 4, .subs .r3 .r3 (imm 1)]

theorem wordStep_ok (s : State) {S D : BitVec 32} {i w : Nat} (hs : s.gpr .r1 = S + BitVec.ofNat 32 (4 * i))
    (hd : s.gpr .r2 = D + BitVec.ofNat 32 (4 * i)) (hn : s.gpr .r3 = BitVec.ofNat 32 w)
    (r : InRegions (s.rd ++ s.wr) (State.addr (S + BitVec.ofNat 32 (4 * i))) 4)
    (wr : InRegions s.wr (State.addr (D + BitVec.ofNat 32 (4 * i))) 4) :
    ∃ s', runBlock isa wordBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 (4 * i)))
        (s.mem.readW (State.addr (S + BitVec.ofNat 32 (4 * i))) 32) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (4 * (i + 1)) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (4 * (i + 1)) ∧
      s'.gpr .r3 = BitVec.ofNat 32 w - BitVec.ofNat 32 1 ∧ s'.z = (BitVec.ofNat 32 w - BitVec.ofNat 32 1 == 0) ∧
      Keeps s s' := by
  have e (P : BitVec 32) : P + BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4 = P + BitVec.ofNat 32 (4 * (i + 1)) := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.mul_succ]
  refine ⟨_, by arun [hs, hd, hn, add_ofNat_zero, r, wr], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, Arm.mem_store]
  · simp [gpr_setReg, hs, e]
  · simp [gpr_setReg, hd, e]
  · simp [gpr_setReg, hn]
  · simp [z_setReg, hn]
  · refine ⟨fun r h => ?_, rfl, rfl, rfl⟩
    simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    simp [gpr_setReg, h₁, h₂, h₃, h₄]

/-- What the word loop needs: `k ≥ 1` words at `S` to copy to `D`, apart. -/
structure WordsPre (s : State) (S D : BitVec 32) (k : Nat) : Prop where
  r1 : s.gpr .r1 = S
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 k
  pos : 1 ≤ k
  fitS : S.toNat + 4 * k ≤ 2 ^ 32
  fitD : D.toNat + 4 * k ≤ 2 ^ 32
  rd : Covers [⟨State.addr S, 4 * k⟩] (s.rd ++ s.wr)
  wr : Covers [⟨State.addr D, 4 * k⟩] s.wr
  disj : (⟨State.addr S, 4 * k⟩ : Region).Disjoint ⟨State.addr D, 4 * k⟩

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
    WP isa copyWords s fun s' => s'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * k)) ∧
      s'.gpr .r1 = S + BitVec.ofNat 32 (4 * k) ∧ s'.gpr .r2 = D + BitVec.ofNat 32 (4 * k) ∧ Keeps s s' := by
  have hS := h.fitS
  have hD := h.fitD
  refine WP.loop (M := isa) (body := .block wordBody) (c := .ne)
    (fun (w : Nat) (t : State) => ∃ i, w = k - i ∧ i < k ∧ t.gpr .r1 = S + BitVec.ofNat 32 (4 * i) ∧
      t.gpr .r2 = D + BitVec.ofNat 32 (4 * i) ∧ t.gpr .r3 = BitVec.ofNat 32 (k - i) ∧
      t.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * i)) ∧ Keeps s t) ?_ (k - 0) _
    ⟨0, rfl, h.pos, by rw [h.r1]; simp, by rw [h.r2]; simp, by rw [h.r3, Nat.sub_zero],
      by simp [bytesAt, writeBytes_nil], Keeps.refl s⟩
  rintro w t ⟨i, rfl, hi, r1, r2, r3, mem, kp⟩
  have hin : 4 * i + 4 ≤ 4 * k := by omega
  have aS : State.addr (S + BitVec.ofNat 32 (4 * i)) = State.addr S + BitVec.ofNat 64 (4 * i) := addr_add (by omega)
  have aD : State.addr (D + BitVec.ofNat 32 (4 * i)) = State.addr D + BitVec.ofNat 64 (4 * i) := addr_add (by omega)
  have cov (rs : List Region) (P : Addr) (hc : Covers [⟨P, 4 * k⟩] rs) : InRegions rs (P + BitVec.ofNat 64 (4 * i)) 4 :=
    hc _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base P hin (by omega)⟩
  obtain ⟨t', run', mem', r1', r2', r3', z', kp'⟩ := wordStep_ok t (w := k - i) r1 r2 r3
    (by rw [kp.rd, kp.wr, aS]; exact cov _ _ h.rd) (by rw [kp.wr, aD]; exact cov _ _ h.wr)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hk32 : k < 2 ^ 32 := by omega
  have hmem : t'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * (i + 1))) := by
    rw [mem', mem, aS, aD, Mem.readW, read_kept h.disj hin (by omega), ← Mem.readW, writeW_readW,
      show 4 * (i + 1) = 4 * i + 4 by omega, bytesAt_append,
      ← writeBytes_append _ _ _ _ (by simp [Proof.Cmac.bytesAt_length]; omega), Proof.Cmac.bytesAt_length]
  have hz : t'.z = decide (i + 1 = k) := by rw [z', dec32 hi hk32, z_dec hi hk32]
  have ev : isa.eval .ne t' = some !decide (i + 1 = k) := eval_ne' hz
  by_cases he : i + 1 = k
  · left
    refine ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [r1', he], by rw [r2', he], kp.trans kp'⟩
  · right
    refine ⟨by rw [ev]; simp [he], k - (i + 1), by omega, i + 1, rfl, by omega, r1', r2',
      by rw [r3', dec32 hi hk32], hmem, kp.trans kp'⟩

theorem shr2 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 2 = BitVec.ofNat 32 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem and3 {n : Nat} (hn : n < 2 ^ 32) : BitVec.ofNat 32 n &&& BitVec.ofNat 32 3 = BitVec.ofNat 32 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show 3 < 2 ^ 32 by decide), Nat.mod_eq_of_lt (by omega),
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- A run keeps a register no instruction of the code writes. -/
theorem WP.keepGpr {c : Prog isa} {s : State} {Q : State → Prop} {r : Reg} (h : WP isa c s Q)
    (hc : ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.gpr hc he (.inl hn)⟩

/-- What the copy of the slice that the descriptor at `A₀` lists needs: its
address `S` and length `n` there, `n` bytes at `S` to copy to `D`, apart, and
the descriptor apart from them. -/
structure SlicePre (s : State) (A₀ S D : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = A₀
  r2 : s.gpr .r2 = D
  d0 : InRegions (s.rd ++ s.wr) (State.addr A₀) 4
  d4 : InRegions (s.rd ++ s.wr) (State.addr (A₀ + BitVec.ofNat 32 4)) 4
  w0 : s.mem.readW (State.addr A₀) 32 = S
  w4 : s.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 n
  lt : n < 2 ^ 32
  fitS : S.toNat + n ≤ 2 ^ 32
  fitD : D.toNat + n ≤ 2 ^ 32
  rd : Covers [⟨State.addr S, n⟩] (s.rd ++ s.wr)
  wr : 0 < n → Covers [⟨State.addr D, n⟩] s.wr
  disj : (⟨State.addr S, n⟩ : Region).Disjoint ⟨State.addr D, n⟩
  dd : (⟨State.addr (A₀ + BitVec.ofNat 32 4), 4⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem wordsArg_ok (s : State) {A₀ : BitVec 32} (h0 : s.gpr .r0 = A₀)
    (d0 : InRegions (s.rd ++ s.wr) (State.addr A₀) 4)
    (d4 : InRegions (s.rd ++ s.wr) (State.addr (A₀ + BitVec.ofNat 32 4)) 4) :
    ∃ s', runBlock isa wordsArg s = some s' ∧ s'.gpr .r1 = s.mem.readW (State.addr A₀) 32 ∧
      s'.gpr .r3 = s.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 >>> 2 ∧
      s'.z = ((s.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 >>> 2) - 0 == 0) ∧
      (∀ r, r ≠ .r1 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by arun [wordsArg, h0, add_ofNat_zero, d0, d4], ?_, ?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | simp [gpr_setReg, h₁, h₂]
    | simp [gpr_setReg]

theorem bytesArg_ok (s : State) {A₀ : BitVec 32} (h0 : s.gpr .r0 = A₀)
    (d4 : InRegions (s.rd ++ s.wr) (State.addr (A₀ + BitVec.ofNat 32 4)) 4) :
    ∃ s', runBlock isa bytesArg s = some s' ∧
      s'.gpr .r3 = s.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 &&& BitVec.ofNat 32 3 ∧
      s'.z = ((s.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 &&& BitVec.ofNat 32 3) - 0 == 0) ∧
      (∀ r, r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by arun [bytesArg, h0, d4], ?_, ?_, fun r h₁ => ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | rfl
    | simp [gpr_setReg, h₁]
    | simp [gpr_setReg]

theorem toNat_add_of_lt {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem z_ne0 {k : Nat} (hk : k < 2 ^ 32) : (BitVec.ofNat 32 k - 0 == 0) = decide (k = 0) := by
  rw [show (BitVec.ofNat 32 k - 0 : BitVec 32) = BitVec.ofNat 32 k from BitVec.sub_zero _]; exact z_cmp0 hk

/-- `copySlice`: the `n` bytes at `S` to `D`, and `r2` past them. -/
theorem copySlice_wp (s : State) {A₀ S D : BitVec 32} {n : Nat} (h : SlicePre s A₀ S D n) :
    WP isa copySlice s fun s' => s'.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) n) ∧
      s'.gpr .r2 = D + BitVec.ofNat 32 n ∧ Keeps s s' := by
  have hn := h.lt
  have hfS := h.fitS
  have hfD := h.fitD
  have hqr : 4 * (n / 4) + n % 4 = n := by omega
  obtain ⟨s₁, run₁, r1₁, r3₁, z₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := wordsArg_ok s h.r0 h.d0 h.d4
  rw [h.w0] at r1₁
  rw [h.w4, shr2 hn] at r3₁ z₁
  rw [z_ne0 (by omega)] at z₁
  have kp₁ : Keeps s s₁ := ⟨fun r hr => g₁ r (by intro e; subst e; simp [copyRegs] at hr)
    (by intro e; subst e; simp [copyRegs] at hr), sp₁, rd₁, wr₁⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  -- The whole words.
  have hblk : WP isa (.ite .eq (.block []) copyWords) s₁ fun s₂ =>
      s₂.mem = writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * (n / 4))) ∧
      s₂.gpr .r1 = S + BitVec.ofNat 32 (4 * (n / 4)) ∧ s₂.gpr .r2 = D + BitVec.ofNat 32 (4 * (n / 4)) ∧
      s₂.gpr .r0 = A₀ ∧ Keeps s s₂ := by
    refine WP.ite (decide (n / 4 = 0)) (eval_eq' z₁) (fun ht => ?_) (fun hf => ?_)
    · have h0 : n / 4 = 0 := by simpa using ht
      refine WP.block_nil ⟨?_, ?_, ?_, ?_, kp₁⟩
      · rw [m₁, h0, Nat.mul_zero]; simp [bytesAt, writeBytes_nil]
      · rw [r1₁, h0]; simp
      · rw [g₁ _ (by decide) (by decide), h.r2, h0]; simp
      · rw [g₁ _ (by decide) (by decide), h.r0]
    · have h0 : n / 4 ≠ 0 := by simpa using hf
      have hw : WordsPre s₁ S D (n / 4) :=
        ⟨r1₁, by rw [g₁ _ (by decide) (by decide), h.r2], r3₁, by omega, by omega, by omega,
          by rw [rd₁, wr₁]; exact covers_prefix h.rd (by omega),
          by rw [wr₁]; exact covers_prefix (h.wr (by omega)) (by omega),
          (h.disj.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))⟩
      refine WP.mono (WP.keepGpr (r := .r0) (copyWords_ok s₁ hw) (by decide) (by decide))
        fun s₂ ⟨⟨m₂, r1₂, r2₂, kp₂⟩, r0₂⟩ => ⟨?_, r1₂, r2₂, ?_, kp₁.trans kp₂⟩
      · rw [m₂, m₁]
      · rw [r0₂, g₁ _ (by decide) (by decide), h.r0]
  refine WP.seq (WP.mono hblk fun s₂ ⟨m₂, r1₂, r2₂, r0₂, kp₂⟩ => ?_)
  -- The last `n mod 4` bytes.
  have hlen : (bytesAt s.mem (State.addr S) (4 * (n / 4))).length = 4 * (n / 4) := Proof.Cmac.bytesAt_length _ _ _
  have hfr : Frame [⟨State.addr D, n⟩] s.mem s₂.mem := by
    rw [m₂]
    refine writeBytes_frame _ _ _ ?_
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, hlen]
    omega
  have w4₂ : s₂.mem.readW (State.addr (A₀ + BitVec.ofNat 32 4)) 32 = BitVec.ofNat 32 n := by
    rw [hfr.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.dd) (by decide), h.w4]
  obtain ⟨s₃, run₃, r3₃, z₃, g₃, m₃, sp₃, rd₃, wr₃⟩ :=
    bytesArg_ok s₂ r0₂ (by rw [kp₂.rd, kp₂.wr]; exact h.d4)
  rw [w4₂, and3 hn] at r3₃ z₃
  rw [z_ne0 (by omega)] at z₃
  have kp₃ : Keeps s s₃ := kp₂.trans ⟨fun r hr => g₃ r (by intro e; subst e; simp [copyRegs] at hr), sp₃, rd₃,
    wr₃⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hS : (⟨State.addr S + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨State.addr S, n⟩ :=
    Offset.sub_base _ (by omega)
  have hD : (⟨State.addr D + BitVec.ofNat 64 (4 * (n / 4)), n % 4⟩ : Region).Sub ⟨State.addr D, n⟩ :=
    Offset.sub_base _ (by omega)
  have hrest : bytesAt s₃.mem (State.addr S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) =
      bytesAt s.mem (State.addr S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4) := by
    rw [m₃]
    refine Proof.AesGcm.Arm.bytesAt_frame hfr (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.disj.sub_left hS
  have hend : D + BitVec.ofNat 32 (4 * (n / 4)) + BitVec.ofNat 32 (n % 4) = D + BitVec.ofNat 32 n := by
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, hqr]
  have hall : writeBytes (writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * (n / 4))))
      (State.addr D + BitVec.ofNat 64 (4 * (n / 4)))
      (bytesAt s.mem (State.addr S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4)) =
      writeBytes s.mem (State.addr D) (bytesAt s.mem (State.addr S) n) := by
    have e := writeBytes_append s.mem (State.addr D) (bytesAt s.mem (State.addr S) (4 * (n / 4)))
      (bytesAt s.mem (State.addr S + BitVec.ofNat 64 (4 * (n / 4))) (n % 4))
      (by rw [hlen, Proof.Cmac.bytesAt_length]; omega)
    rw [hlen] at e
    rw [e, ← bytesAt_append, hqr]
  refine WP.ite (decide (n % 4 = 0)) (eval_eq' z₃) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 4 = 0 := by simpa using ht
    refine WP.block_nil ⟨?_, ?_, kp₃⟩
    · rw [m₃, m₂, ← hall, h0]; simp [bytesAt, writeBytes_nil]
    · rw [g₃ _ (by decide), r2₂, ← hend, h0]; simp
  · have h0 : n % 4 ≠ 0 := by simpa using hf
    have aS : State.addr (S + BitVec.ofNat 32 (4 * (n / 4))) = State.addr S + BitVec.ofNat 64 (4 * (n / 4)) :=
      addr_add (by omega)
    have aD : State.addr (D + BitVec.ofNat 32 (4 * (n / 4))) = State.addr D + BitVec.ofNat 64 (4 * (n / 4)) :=
      addr_add (by omega)
    have lp : LoopPre s₃ (S + BitVec.ofNat 32 (4 * (n / 4))) (D + BitVec.ofNat 32 (4 * (n / 4))) (n % 4) :=
      ⟨by rw [g₃ _ (by decide), r1₂], by rw [g₃ _ (by decide), r2₂], r3₃, by omega, by omega,
        by rw [toNat_add_of_lt (by omega)]; omega, by rw [toNat_add_of_lt (by omega)]; omega,
        by rw [rd₃, wr₃, kp₂.rd, kp₂.wr, aS]; exact covers_off h.rd (by omega) (by omega),
        by rw [wr₃, kp₂.wr, aD]; exact covers_off (h.wr (by omega)) (by omega) (by omega),
        by rw [aS, aD]; exact (h.disj.sub_left hS).sub_right hD⟩
    refine WP.mono (WP.keepGpr (r := .r0) (copyLoop_ok s₃ lp) (by decide) (by decide))
      fun s₄ ⟨⟨m₄, lo⟩, r0₄⟩ => ⟨?_, by rw [lo.r2, hend], kp₃.trans ⟨fun r hr => ?_, lo.sp, lo.rd, lo.wr⟩⟩
    · rw [m₄, aS, aD, hrest, m₃, m₂, hall]
    · simp only [copyRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h₁, h₂, h₃, h₄⟩ := hr
      by_cases h₀ : r = .r0
      · subst h₀; exact r0₄
      · exact lo.other r h₀ h₁ h₂ h₃ h₄

end VG.Proof.AesGcm.Arm.Gather
