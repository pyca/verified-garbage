module

import VerifiedGarbage.Proof.Aes.RISCV64.Prologue
public import VerifiedGarbage.Proof.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Aes.RISCV64.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Impl.Aes.RISCV64.Ctr32
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES counter mode on RISC-V, with the round keys bitsliced

`vg_aes_ctr32_bs` and `vg_aes_ctr32_bs_to` (`Impl/Aes/RISCV64/Ctr32.lean`)
are `vg_aes_ctr32` and `vg_aes_ctr32_to` with the round keys given bitsliced,
as `vg_aes_gcm_bitslice` leaves them. Their contracts state the result for
every key schedule whose round keys `0 … rounds` are the bitsliced keys
(`KeysAt`): all such schedules give the same cipher (`aesWith_congr`).

The prologue is `Ctr32.lean`'s but for our return address, which is always
saved. From eight blocks up, a loop (`bsConvLoop_ok`) writes the round keys
that `encrypt4` takes to the scratch buffer, and the groups are
`vg_aes_ctr32`'s; with fewer, they are `groupsK_ok` with the round keys
outside the scratch buffer and `ra`, which `encrypt4K .ra` compares with the
round key pointer (`bsKb_wp`).
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## Schedules with the same round keys -/

theorem cipher_congr {nr : Nat} {w w' : List Byte}
    (h : ∀ j ≤ nr, ∀ i < 16, (roundKey w j).getD i 0 = (roundKey w' j).getD i 0)
    (x : Spec.Aes.State) : Spec.Aes.cipher nr w x = Spec.Aes.cipher nr w' x := by
  have hark : ∀ j ≤ nr, ∀ s, Spec.Aes.addRoundKey s (roundKey w j) =
      Spec.Aes.addRoundKey s (roundKey w' j) :=
    fun j hj s => by
      unfold Spec.Aes.addRoundKey; congr 1; funext i; rw [h j hj i i.isLt]
  have hf : ∀ (l : List Nat), (∀ j ∈ l, j + 1 ≤ nr) → ∀ s,
      l.foldl (fun s j => Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows
        (Spec.Aes.subBytes s))) (roundKey w (j + 1))) s =
        l.foldl (fun s j => Spec.Aes.addRoundKey (Spec.Aes.mixColumns (Spec.Aes.shiftRows
          (Spec.Aes.subBytes s))) (roundKey w' (j + 1))) s := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons a l ih =>
      intro hl s
      simp only [List.foldl_cons]
      rw [hark (a + 1) (hl a List.mem_cons_self)]
      exact ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _
  simp only [Spec.Aes.cipher]
  rw [hark 0 (Nat.zero_le _), hark nr (Nat.le_refl _),
    hf _ (fun j hj => by rw [List.mem_range] at hj; omega_using [hj])]

/-- Two schedules whose round keys `0 … R` are the same bitsliced keys give
the same cipher. -/
theorem aesWith_congr {m : Mem} {K0 : Addr} {R : Nat} {w w' : List Byte} (h : KeysAt m K0 R w)
    (h' : KeysAt m K0 R w') : Spec.Gcm.aesWith R w = Spec.Gcm.aesWith R w' := by
  funext x
  unfold Spec.Gcm.aesWith
  rw [cipher_congr (w := w) (w' := w') (fun j hj i hi => by
    refine byte_ext fun t ht => ?_
    rw [← getD_rkState _ hi, ← getD_rkState _ hi]
    exact (h j hj t ht i hi 0 (by decide)).symm.trans (h' j hj t ht i hi 0 (by decide)))]

end VG.Proof.Aes.RISCV64

namespace VG.Proof.Aes

open Spec.Gcm

open VG.RISCV64 in
/-- RISC-V contract for the internal `vg_aes_ctr32_bs(keys: *const [u64; 120],
rounds: usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize,
scratch: *mut [u64; 256])`: `ctr32RISCV64` with the round keys bitsliced, 64
bytes each, at `keys` (a multiple of 8): XORs the counter-mode keystream of
every key schedule whose round keys `0 … rounds` they are into the `n` blocks
at `data`, and advances the counter block by `n`.

The code may read `keys` (960 bytes) and read and write `counter`, `data` and
`scratch`, which overlap none of each other. The pointers, `rounds` and `n`
are public; the round keys, the counter block and the data are secret. -/
def ctr32BsRISCV64 : Contract RISCV64.isa where
  pre s :=
    let keys : Region := ⟨s.gpr .a0, 960⟩
    let counter : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 2048⟩
    s.rd = [keys] ∧ s.wr = [counter, data, scratch] ∧
    keys.Disjoint counter ∧ keys.Disjoint data ∧ keys.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ ∃ w, RISCV64.KeysAt s.mem (s.gpr .a0) (s.gpr .a1).toNat w
  post s s' := ∀ w, RISCV64.KeysAt s.mem (s.gpr .a0) (s.gpr .a1).toNat w →
    blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
        ctr32 (aesWith (s.gpr .a1).toNat w) (blockAt s.mem (s.gpr .a2))
          (blocksAt s.mem (s.gpr .a3) (s.gpr .a4).toNat) ∧
      blockAt s'.mem (s.gpr .a2) = Nat.repeat inc32 (s.gpr .a4).toNat (blockAt s.mem (s.gpr .a2))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for the internal `vg_aes_ctr32_bs_to(keys: *const [u64;
120], rounds: usize, counter: *mut [u8; 16], dst: *mut [u8; 16], n: usize,
scratch: *mut [u64; 256], src: *const [u8; 16])`: `ctr32BsRISCV64` out of
place, XORing the keystream into the `n` blocks at `src` and writing the
result to the `n` blocks at `dst`.

The code may read `keys` (960 bytes) and `src` (`16 n` bytes), and read and
write `counter`, `dst` and `scratch`. The source and destination are identical
or disjoint. Neither buffer wraps around the end of the address space.
The pointers, `rounds` and `n` are public; the round keys, the
counter block and the data are secret. -/
def ctr32BsToRISCV64 : Contract RISCV64.isa where
  pre s :=
    let keys : Region := ⟨s.gpr .a0, 960⟩
    let counter : Region := ⟨s.gpr .a2, 16⟩
    let data : Region := ⟨s.gpr .a3, 16 * (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 2048⟩
    let src : Region := ⟨s.gpr .a6, 16 * (s.gpr .a4).toNat⟩
    s.rd = [keys, src] ∧ s.wr = [counter, data, scratch] ∧
    keys.Disjoint counter ∧ keys.Disjoint data ∧ keys.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    src.Disjoint counter ∧ (s.gpr .a6 = s.gpr .a3 ∨ src.Disjoint data) ∧ src.Disjoint scratch ∧
    (s.gpr .a3).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a6).toNat + 16 * (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .a1).toNat = 10 ∨ (s.gpr .a1).toNat = 12 ∨ (s.gpr .a1).toNat = 14) ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ ∃ w, RISCV64.KeysAt s.mem (s.gpr .a0) (s.gpr .a1).toNat w
  post s s' := ∀ w, RISCV64.KeysAt s.mem (s.gpr .a0) (s.gpr .a1).toNat w →
    blocksAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
        ctr32 (aesWith (s.gpr .a1).toNat w) (blockAt s.mem (s.gpr .a2))
          (blocksAt s.mem (s.gpr .a6) (s.gpr .a4).toNat) ∧
      blockAt s'.mem (s.gpr .a2) = Nat.repeat inc32 (s.gpr .a4).toNat (blockAt s.mem (s.gpr .a2))
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.RISCV64.Align VG.RISCV64.Steps VG.Bitslice
  VG.Impl.Aes.RISCV64 VG.Proof.Aes

open VG.Spec.Aes (roundKey)

/-! ## The prologue's other steps -/

/-- Our return address into its slot. -/
theorem bsSave_wp {s : State} {X b : Addr} (hs : Scr s X 2048) (hb : s.gpr sb = b)
    {P : State → Prop}
    (h : ∀ s', (∀ r, s'.gpr r = s.gpr r) → Frame [⟨raSlotAddr b, 8⟩] s.mem s'.mem →
      s'.mem.readW (raSlotAddr b) 64 = s.gpr .ra → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      P s') :
    WP isa (.block bsSave) s P := by
  simp only [bsSave, srcSlot, stS]
  refine wp_sd (by decide) (by rw [hb]) (by rw [← hb]; exact wordAddr_al hs.al 62 (by decide))
    ⟨_, hs.wr, by rw [← hb]; exact hs.contains (by decide) (by decide)⟩ fun s' u => WP.block_nil ?_
  refine h s' (fun r => by rw [u.gpr]) ?_ (by rw [u.mem, Mem.readW_writeW_self64]) u.rd u.wr u.sp
  rw [u.mem]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

/-- Out of place, the source (`a6`) into `a2`. -/
theorem bsSrc_wp {o : Bool} {s : State} {P : State → Prop}
    (h : ∀ s', (o = true → s'.gpr .a2 = s.gpr .a6) →
      (∀ r, r ≠ .a2 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → P s') :
    WP isa (.block (bsSrc o)) s P := by
  cases o
  · exact WP.block_nil (h s (fun h => absurd h (by decide)) (fun _ _ => rfl) rfl rfl rfl rfl)
  · simp only [bsSrc, movR, ite_true]
    exact wp_mv fun s' u => WP.block_nil (h s' (fun _ => u.gpr) u.other u.mem u.rd u.wr u.sp)

theorem ofNat_shl6 {R : Nat} (h : R < 2 ^ 58) : BitVec.ofNat 64 R <<< 6 = BitVec.ofNat 64 (64 * R) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (a := R) (by omega_using [h])]
  congr 1; omega_using []

/-- `ra := a0 + 64 rounds - lastKey`: the first round key at byte
`lastKey - 64 rounds` from `ra`. -/
theorem bsKb_wp {s : State} {R : Nat} (hR : s.gpr .a1 = BitVec.ofNat 64 R) (hR' : R ≤ 14)
    {P : State → Prop}
    (h : ∀ s', s.gpr .a0 = s'.gpr .ra + BitVec.ofNat 64 (1920 - 64 * R) →
      (∀ r, r ≠ t0 → r ≠ .ra → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block bsKb) s P := by
  unfold bsKb shlI
  refine wp_sll (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_subi (imm := lastKey) (by decide)
    fun s₃ u₃ => WP.block_nil ?_
  refine h s₃ ?_ (fun r h1 h2 => ?_) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr]) (by rw [u₃.sp, u₂.sp, u₁.sp])
  · rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), u₁.gpr, hR, ofNat_shl6 (by omega_using [hR'])]
    simp only [lastKey]
    bv_omega
  · rw [u₃.other _ h2, u₂.other _ h2, u₁.other _ h1]

/-! ## The round keys of `encrypt4` from the bitsliced ones -/

/-- Where the loop runs: the scratch buffer at `X`, rounded to `b`, with the
masks; the bitsliced round keys of `w` at `K`. -/
structure CSetup (s₀ : State) (X b K : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : Scr s₀ X 2048
  base : s₀.gpr sb = b
  masks : MasksAt s₀.mem b allKs
  key : (⟨K, 960⟩ : Region) ∈ s₀.rd ++ s₀.wr
  kal : K.toNat % 8 = 0
  sep : Region.Disjoint ⟨K, 960⟩ ⟨X, 2048⟩
  rounds : R ≤ 14
  keys : KeysAt s₀.mem K R w

/-- Before round key `j`. -/
structure CInv (s₀ : State) (b K : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  a1 : s.gpr .a1 = BitVec.ofNat 64 (j + 1)
  a0 : s.gpr .a0 = K + BitVec.ofNat 64 (64 * j)
  a2 : s.gpr .a2 = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame (kRegions b) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRelF i (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

theorem bsStep_ok (s : State) :
    WP isa (.block bsStep) s fun s' =>
      s'.gpr .a0 = s.gpr .a0 - 64 ∧ s'.gpr .a2 = s.gpr .a2 - 64 ∧ s'.gpr .a1 = s.gpr .a1 - 1 ∧
      (∀ r, r ≠ .a0 → r ≠ .a2 → r ≠ .a1 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold bsStep
  refine wp_subi (imm := 64) (by decide) fun s₁ u₁ => wp_subi (imm := 64) (by decide) fun s₂ u₂ =>
    wp_subi (imm := 1) (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, fun r h1 h2 h3 => ?_,
      u₃.mem.trans (u₂.mem.trans u₁.mem), u₃.rd.trans (u₂.rd.trans u₁.rd),
      u₃.wr.trans (u₂.wr.trans u₁.wr), u₃.sp.trans (u₂.sp.trans u₁.sp)⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]; rfl
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; rfl
  · rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1]

theorem bsConvBody_ok {s₀ : State} {X b K : Addr} {R : Nat} {w : List Byte}
    (hk : CSetup s₀ X b K R w) {j : Nat} {s : State} (hi : CInv s₀ b K R w j s) :
    WP isa bsConvBody s fun s' =>
      (j = 0 ∧ isa.eval (.nonzero .a1) s' = some false ∧ FDone s₀ b R w s') ∨
      (0 < j ∧ isa.eval (.nonzero .a1) s' = some true ∧ CInv s₀ b K R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  obtain hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  obtain hscr : Scr s X 2048 := hk.scr.congr hi.wr (by rw [hsb, hk.base])
  have hin : ∀ i ≤ R, ∀ k < 8, (⟨K, 960⟩ : Region).Contains (wordAddr (K + BitVec.ofNat 64 (64 * i)) k) (64 / 8) :=
    fun i hi k hk' => by
      rw [wordAddr, Offset.add_add]
      exact Offset.contains_base K (by omega_arith) (by omega_arith)
  have kat : KeysAt s.mem K R w := keysAt_frameK hi.frame
    (fun r hr => hk.sep.sub_right (frame_regions hk.scr hk.base r hr)) hin hk.keys
  simp only [bsConvBody]
  -- Load the round key.
  refine WP.seq ?_
  rw [WP.block_append_iff (M := isa)]
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hsp₁, hoth₁, hfr₁⟩ := bsLoad_ok (s := s)
    { slotIn := fun k hk' => by simp [bsLoadCfg] at hk'
      extIn := fun k hk' => ⟨_, by rw [hi.rd, hi.wr]; exact hk.key, by
        show (⟨K, 960⟩ : Region).Contains (wordAddr (s.gpr .a0) k) 8
        rw [hi.a0]; exact hin j hjR k hk'⟩
      baseAl := fun _ => hscr.al
      extAl := fun _ => by
        show (s.gpr .a0).toNat % 8 = 0
        rw [hi.a0, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := hk.kal
        omega_arith
      slots := by simp [bsLoadCfg]
      sep := fun k hk' => by simp [bsLoadCfg] at hk' }
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  obtain hm₁ : s₁.mem = s.mem := by
    funext x
    exact hfr₁ x fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      simp [slotRegion, bsLoadCfg, Region.Contains] at hc
  have hbs₁ : BsRel (Q s₁) fun _ => rkState (roundKey w j) :=
    (kat j hjR).congrW fun i hi' => by rw [hq₁ i hi', hi.a0]
  refine Steps.wp_andi (by decide) fun s₁' u₁ => WP.block_nil ?_
  have ko₁ : ∀ r, r ∉ sboxWrites → s₁'.gpr r = s.gpr r := fun r hr =>
    (u₁.other r fun e => hr (e ▸ by decide)).trans (hoth₁ r hr)
  obtain hsb₁ : s₁'.gpr sb = b := by rw [ko₁ sb (by decide), hsb]
  obtain hscr₁ : Scr s₁' X 2048 := hscr.congr (u₁.wr.trans hwr₁) (by rw [hsb₁, hsb])
  have hbs₁' : BsRel (Q s₁') fun _ => rkState (roundKey w j) :=
    hbs₁.congrW fun i _ => (u₁.other _ (q_ne_t0 i)).symm
  -- The odd ones to form 1.
  refine WP.seq (WP.mono (Q := fun (s₂ : State) =>
      Proof.Aes.BsRel 4 (decide (j % 2 = 1)) (Q s₂) (fun _ => rkState (roundKey w j)) ∧
      (∀ r, r ∉ sboxWrites → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.sp = s.sp)
    ?_ fun s₂ ⟨hbs₂, hoth₂, hm₂, hrd₂, hwr₂, hsp₂⟩ => ?_)
  · have ev : isa.eval (.nonzero t0) s₁' = some (decide (j % 2 = 0)) := by
      rw [Steps.eval_nonzero, u₁.gpr, hoth₁ .a1 (by decide), hi.a1, odd_bit j (by omega_arith)]
    refine WP.ite _ ev (fun h => ?_) (fun h => ?_)
    · have h0 : j % 2 = 0 := by simpa using h
      refine WP.block_nil ⟨?_, ko₁, u₁.mem.trans hm₁, u₁.rd.trans hrd₁, u₁.wr.trans hwr₁, u₁.sp.trans hsp₁⟩
      rw [decide_eq_false (by omega_arith : ¬ j % 2 = 1)]
      exact hbs₁'
    · have h1 : j % 2 = 1 := by
        have : ¬ j % 2 = 0 := by simpa using h
        omega_arith
      have hks : MasksAt s₁'.mem (s₁'.gpr sb) srKs := by
        rw [u₁.mem, hm₁, hsb₁]
        exact masksAt_sub (masks_kept hi.frame hk.masks) fun p hp => by
          simp only [allKs, List.mem_append]; exact .inl (.inr hp)
      obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hfr₂⟩ :=
        invShiftRows_ok (hscr₁.okExts rfl rfl rfl (by decide) (by decide)) hks
      have hm₂ : s₂.mem = s₁'.mem := by
        funext x
        exact hfr₂ x fun r hr hc => by
          simp only [List.mem_singleton] at hr; subst hr
          simp [slotRegion, srCfg, Region.Contains] at hc
      refine WP.of_runBlock ⟨s₂, hs₂, ?_, fun r hr => (hoth₂ r hr).trans (ko₁ r hr),
        hm₂.trans (u₁.mem.trans hm₁), hrd₂.trans (u₁.rd.trans hrd₁), hwr₂.trans (u₁.wr.trans hwr₁),
        hsp₂.trans (u₁.sp.trans hsp₁)⟩
      rw [decide_eq_true h1]
      exact bs_toForm1 hq₂ hbs₁'
  have a1₂ : s₂.gpr .a1 = BitVec.ofNat 64 (j + 1) := by
    rw [hoth₂ _ (by decide), hi.a1]
  refine WP.seq (Steps.wp_subi (imm := 1) (by decide) fun s₂' u₂ => WP.block_nil ?_)
  have t₂ : s₂'.gpr t0 = BitVec.ofNat 64 j := by
    rw [u₂.gpr, a1₂]; exact ofNat_succ_sub_one j
  have hq₂' : ∀ i < 8, Q s₂' i = Q s₂ i := fun i _ => u₂.other _ (q_ne_t0 i)
  -- The constant.
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => KeyRelF j (Q s₃) (roundKey w j) ∧
      (∀ r, r ∉ sboxWrites → s₃.gpr r = s₂.gpr r) ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.sp = s₂.sp ∧
      Frame [⟨b, 320⟩] s₂.mem s₃.mem) ?_ fun s₃ ⟨hkr, hoth₃, hrd₃, hwr₃, hsp₃, hfr₃⟩ => ?_)
  · have ko : ∀ r, r ∉ sboxWrites → s₂'.gpr r = s₂.gpr r := fun r hr =>
      u₂.other r fun e => hr (e ▸ by decide)
    refine WP.ite (decide (j ≠ 0)) (eval_nonzero_ofNat t₂ (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have h0 : j ≠ 0 := by simpa using h
      have hsb₂ : s₂'.gpr sb = b := by rw [ko sb (by decide), hoth₂ sb (by decide), hsb]
      obtain ⟨s₃, hs₃, h₃, hrd₃, hwr₃, hsp₃, hoth₃, hfr₃⟩ := add63_ok
        ((hscr.congr (s' := s₂') (u₂.wr.trans hwr₂) (hsb₂.trans hsb.symm)).okSlots rfl rfl rfl (by decide) (by decide))
      refine WP.of_runBlock ⟨s₃, hs₃, ?_, fun r hr => (hoth₃ r hr).trans (ko r hr), hrd₃.trans u₂.rd,
        hwr₃.trans u₂.wr, hsp₃.trans u₂.sp, ?_⟩
      · unfold KeyRelF
        simp only [h0, ite_false]
        exact (hbs₂.congrW fun i hi => (hq₂' i hi).symm).map (· ^^^ 0x63) h₃
      · rw [← u₂.mem]
        have := hfr₃
        simp only [slotRegion, sboxCfg, hsb₂] at this
        exact this
    · have h0 : j = 0 := by simpa using h
      refine WP.block_nil ⟨?_, ko, u₂.rd, u₂.wr, u₂.sp, by rw [u₂.mem]; exact Frame.refl _ _⟩
      unfold KeyRelF
      simp only [h0, ite_true]
      have := hbs₂.congrW fun i hi => (hq₂' i hi).symm
      rw [h0] at this
      exact this
  -- Store it.
  rw [WP.block_append_iff (M := isa)]
  have keep₃ : ∀ r, r ∉ sboxWrites → s₃.gpr r = s.gpr r := fun r hr => by
    rw [hoth₃ r hr, hoth₂ r hr]
  obtain hr5₂ : s₃.gpr .a2 = keyAddr b R j := by rw [keep₃ .a2 (by decide), hi.a2]
  obtain hsb₃ : s₃.gpr sb = b := by rw [keep₃ sb (by decide), hsb]
  obtain hscr₃ : Scr s₃ X 2048 := hscr.congr (by rw [hwr₃, hwr₂]) (by rw [hsb₃, hsb])
  obtain ⟨s₄, hs₄, hst₄, hrd₄, hwr₄, hsp₄, hg₄, hfr₄⟩ := keyStore_ok hscr₃
    (off := 1920 - 64 * (R - j)) (by rw [hr5₂, hsb₃]) (by omega_arith) (by omega_arith)
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  -- Step back.
  refine WP.mono (bsStep_ok s₄) fun s₅ ⟨hr3₅, hr5₅, hr4₅, hoth₅, hm₅, hrd₅, hwr₅, hsp₅⟩ => ?_
  obtain hkeep : ∀ r, r ∉ keyWrites → s₅.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₅ r h2 h3 h4, hg₄, keep₃ r h1, hi.keep r hr]
  have fr₄ : Frame [⟨s₃.gpr .a2, 64⟩] s₃.mem s₅.mem := by rw [hm₅]; exact hfr₄
  have fr₃ : Frame [⟨b, 320⟩] s.mem s₃.mem := by rw [← hm₂]; exact hfr₃
  obtain hfr : Frame (kRegions b) s₀.mem s₅.mem := by
    refine (hi.frame.trans (fr₃.mono fun r hr => by simp at hr; simp [hr])).trans (fr₄.sub fun r hr =>
      ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩)
    simp only [List.mem_singleton] at hr; subst hr
    rw [hr5₂]
    exact Offset.sub b (by omega_arith) (by omega_arith)
  -- The keys stored before.
  obtain hold : ∀ i, j < i → i ≤ R →
      KeyRelF i (fun k => s₅.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRelF_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [readW_off_frame fr₄ fun r hr => ?_, readW_off_frame fr₃ fun r hr => ?_]
    · simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base b (by omega_arith) (by omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hr5₂]
      exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  -- The key stored now.
  obtain hnew : KeyRelF j (fun k => s₅.mem.readW (wordAddr (keyAddr b R j) k) 64) (roundKey w j) :=
    keyRelF_congr hkr fun k hk => by rw [hm₅, ← hr5₂, hst₄ k hk]
  obtain hr4 : s₄.gpr .a1 = BitVec.ofNat 64 (j + 1) := by rw [hg₄, keep₃ .a1 (by decide), hi.a1]
  obtain hr3 : s₄.gpr .a0 = K + BitVec.ofNat 64 (64 * j) := by rw [hg₄, keep₃ .a0 (by decide), hi.a0]
  obtain hr5 : s₄.gpr .a2 = keyAddr b R j := by rw [hg₄, hr5₂]
  obtain hrd : s₅.rd = s₀.rd := by rw [hrd₅, hrd₄, hrd₃, hrd₂, hi.rd]
  obtain hwr : s₅.wr = s₀.wr := by rw [hwr₅, hwr₄, hwr₃, hwr₂, hi.wr]
  obtain hsp : s₅.sp = s₀.sp := by rw [hsp₅, hsp₄, hsp₃, hsp₂, hi.sp]
  obtain hr4' : s₅.gpr .a1 = BitVec.ofNat 64 j := by rw [hr4₅, hr4, ofNat_succ_sub_one]
  obtain hev := eval_nonzero_ofNat hr4' (by omega_arith)
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hev, ⟨by rw [hr5₅, hr5], hrd, hwr, hsp, hkeep, hfr,
      fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega_arith) hiR
  · refine .inr ⟨by omega_arith, by simpa [h0] using hev, ⟨by omega_arith, ?_, ?_, ?_, hrd, hwr, hsp,
      hkeep, hfr, ?_⟩⟩
    · rw [hr4', show j - 1 + 1 = j by omega_arith]
    · rw [hr3₅, hr3, show 64 * (j - 1) = 64 * j - 64 by omega_arith]
      exact add_ofNat_sub K (y := 64) (by omega_arith)
    · rw [hr5₅, hr5]; exact keyAddr_pred b hk.rounds (by omega_arith) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega_arith) hiR

theorem bsConvLoop_ok {s₀ : State} {X b K : Addr} {R : Nat} {w : List Byte}
    (hk : CSetup s₀ X b K R w) {s : State} (hi : CInv s₀ b K R w R s) :
    WP isa (.loop bsConvBody (.nonzero .a1)) s (FDone s₀ b R w) := by
  refine WP.loop (M := isa) (CInv s₀ b K R w) (fun n s hs => ?_) R s hi
  refine WP.mono (bsConvBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨hcf, hd⟩
  · exact .inr ⟨hcf, n - 1, by omega_arith, hi'⟩

/-- The loop's registers; out of place, the source into `ra`. -/
theorem bsConvSetup_wp {o : Bool} {s : State} {R : Nat} {P : State → Prop}
    (h1 : s.gpr .a1 = BitVec.ofNat 64 R) (hR : R ≤ 14)
    (h : ∀ s', (o = true → s'.gpr .ra = s.gpr .a6) →
      s'.gpr .a0 = s.gpr .a0 + BitVec.ofNat 64 (64 * R) → s'.gpr .a2 = s.gpr sb + BitVec.ofNat 64 1920 →
      s'.gpr .a1 = BitVec.ofNat 64 (R + 1) →
      (∀ r, r ≠ t0 → r ≠ .ra → r ≠ .a0 → r ≠ .a1 → r ≠ .a2 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → P s') :
    WP isa (.block (bsMove o ++ bsConvSetup)) s P := by
  rw [WP.block_append_iff (M := isa)]
  refine WP.mono (Q := fun (s' : State) => (o = true → s'.gpr .ra = s.gpr .a6) ∧
      (∀ r, r ≠ .ra → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp)
    ?_ fun s₀ ⟨ra₀, ok₀, m₀, rd₀, wr₀, sp₀⟩ => ?_
  · cases o
    · exact WP.block_nil ⟨fun h => absurd h (by decide), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    · simp only [bsMove, movR, ite_true]
      exact wp_mv fun s' u => WP.block_nil ⟨fun _ => u.gpr, u.other, u.mem, u.rd, u.wr, u.sp⟩
  · unfold bsConvSetup shlI
    refine wp_sll (by decide) fun s₁ u₁ => wp_add fun s₂ u₂ => wp_addi (imm := lastKey) (by decide)
      fun s₃ u₃ => wp_addi (imm := 1) (by decide) fun s₄ u₄ => WP.block_nil ?_
    refine h s₄ (fun ho => ?_) ?_ ?_ ?_ (fun r h1 h2 h3 h4 h5 => ?_)
      (u₄.mem.trans (u₃.mem.trans (u₂.mem.trans (u₁.mem.trans m₀))))
      (u₄.rd.trans (u₃.rd.trans (u₂.rd.trans (u₁.rd.trans rd₀))))
      (u₄.wr.trans (u₃.wr.trans (u₂.wr.trans (u₁.wr.trans wr₀))))
      (u₄.sp.trans (u₃.sp.trans (u₂.sp.trans (u₁.sp.trans sp₀))))
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ra₀ ho]
    · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), u₁.gpr,
        ok₀ _ (by decide), ok₀ _ (by decide), h1, ofNat_shl6 (by omega_using [hR])]
    · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), ok₀ _ (by decide)]
      rfl
    · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ok₀ _ (by decide), h1,
        ← BitVec.ofNat_add]
    · rw [u₄.other _ h4, u₃.other _ h5, u₂.other _ h3, u₁.other _ h1, ok₀ _ h2]

/-! ## The whole function -/

/-- What `ctr32BsWith o` needs: `ctr32BsRISCV64.pre`'s, with the data read
from `S`, which is `a6` out of place and the data in place, apart from the
counter block and the scratch buffer, and equal to or apart from the data;
`w` a schedule whose round keys are the bitsliced keys. -/
structure BPre (o : Bool) (s₀ : State) (S : Addr) (w : List Byte) : Prop where
  keys : (⟨s₀.gpr .a0, 960⟩ : Region) ∈ s₀.rd
  wC : (⟨s₀.gpr .a2, 16⟩ : Region) ∈ s₀.wr
  wD : (⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.wr
  wS : (⟨s₀.gpr .a5, 2048⟩ : Region) ∈ s₀.wr
  src : (⟨S, 16 * (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.rd ++ s₀.wr
  outOf : o = true → s₀.gpr .a6 = S
  inPlace : o = false → S = s₀.gpr .a3
  dKC : Region.Disjoint ⟨s₀.gpr .a0, 960⟩ ⟨s₀.gpr .a2, 16⟩
  dKD : Region.Disjoint ⟨s₀.gpr .a0, 960⟩ ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩
  dKS : Region.Disjoint ⟨s₀.gpr .a0, 960⟩ ⟨s₀.gpr .a5, 2048⟩
  dCD : Region.Disjoint ⟨s₀.gpr .a2, 16⟩ ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩
  dCS : Region.Disjoint ⟨s₀.gpr .a2, 16⟩ ⟨s₀.gpr .a5, 2048⟩
  dDS : Region.Disjoint ⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ ⟨s₀.gpr .a5, 2048⟩
  sC : Region.Disjoint ⟨S, 16 * (s₀.gpr .a4).toNat⟩ ⟨s₀.gpr .a2, 16⟩
  sS : Region.Disjoint ⟨S, 16 * (s₀.gpr .a4).toNat⟩ ⟨s₀.gpr .a5, 2048⟩
  alias : Alias S (s₀.gpr .a3) (s₀.gpr .a4).toNat
  rounds : (s₀.gpr .a1).toNat = 10 ∨ (s₀.gpr .a1).toNat = 12 ∨ (s₀.gpr .a1).toNat = 14
  kal : (s₀.gpr .a0).toNat % 8 = 0
  kw : KeysAt s₀.mem (s₀.gpr .a0) (s₀.gpr .a1).toNat w

theorem ofNat_shr3 {a : Nat} (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> 3 = BitVec.ofNat 64 (a / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_using [h]

/-- The test of eight blocks or more. -/
theorem shr3_wp {s : State} {n : Nat} (hn : n < 2 ^ 64) (h4 : s.gpr .a4 = BitVec.ofNat 64 n)
    {P : State → Prop}
    (h : ∀ s', (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → isa.eval (.nonzero t0) s' = some (decide (8 ≤ n)) → P s') :
    WP isa (.block [shrI t0 .a4 3]) s P := by
  refine wp_srl (by decide) fun s' u => WP.block_nil ?_
  rw [h4, ofNat_shr3 hn] at u
  refine h s' u.other u.mem u.rd u.wr u.sp ?_
  rw [Steps.eval_nonzero_ofNat s' t0 (by omega_using [hn]) u.gpr]
  congr 1; exact decide_eq_decide.mpr (by omega_using [])

/-- The groups, by doublewords if the data's addresses are aligned. -/
theorem bsGroups_ok {o : Bool} {m₀ : Mem} {crypt : Prog isa} {s : State} {X b S D : Addr} {n R : Nat}
    {w : List Byte} {icb : Spec.Gcm.Block} (hs : GSetupK crypt s X b S D n R w icb) (hd : s.gpr .a3 = D)
    (hsr : s.gpr (srcReg o) = S) (hin : o = false → S = D) (hi : GInvK o m₀ s b S D n R w icb 0 s) :
    WP isa (ctrGroups crypt o) s (GDone m₀ s b S D n R w icb) := by
  unfold ctrGroups
  refine WP.seq (alignTest_wp hd hsr hin fun s₇ v u₇ ev => ?_)
  obtain hi₇ := hi.of_t0 u₇
  exact WP.ite _ ev
    (fun h => groupsK_ok hs (fun _ => by simpa using h) hi₇)
    (fun _ => groupsK_ok hs (fun h => Bool.noConfusion h) hi₇)

theorem correctBsWith {o : Bool} {s₀ : State} {S : Addr} {w : List Byte} (hp : BPre o s₀ S w) :
    WP isa (Impl.Aes.RISCV64.ctr32BsWith o) s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        Spec.Gcm.blocksAt s'.mem (s₀.gpr .a3) (s₀.gpr .a4).toNat =
          Spec.Gcm.ctr32 (Spec.Gcm.aesWith (s₀.gpr .a1).toNat w)
            (Spec.Gcm.blockAt s₀.mem (s₀.gpr .a2)) (Spec.Gcm.blocksAt s₀.mem S (s₀.gpr .a4).toNat) ∧
        Spec.Gcm.blockAt s'.mem (s₀.gpr .a2) =
          Nat.repeat Spec.Gcm.inc32 (s₀.gpr .a4).toNat (Spec.Gcm.blockAt s₀.mem (s₀.gpr .a2)) := by
  have hwC := hp.wC
  have hwD := hp.wD
  have hwS := hp.wS
  have dKC := hp.dKC
  have dKD := hp.dKD
  have dKS := hp.dKS
  have dCD := hp.dCD
  have dCS := hp.dCS
  have dDS := hp.dDS
  have hR := hp.rounds
  obtain n16 : 16 * (s₀.gpr .a4).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dCD (s₀.gpr .a2) (by simp [Region.Contains]) ?_
    simp only [Region.Contains]
    have := (s₀.gpr .a2 - s₀.gpr .a3).isLt
    omega_arith
  obtain hR14 : (s₀.gpr .a1).toNat ≤ 14 := by omega_arith
  let X := s₀.gpr .a5
  let b := X + BitVec.ofNat 64 (pad X)
  let R := (s₀.gpr .a1).toNat
  let n := (s₀.gpr .a4).toNat
  let ctr := s₀.gpr .a2
  let D := s₀.gpr .a3
  let BK := s₀.gpr .a0
  obtain dCb : Region.Disjoint ⟨ctr, 16⟩ ⟨b, 2040⟩ := dCS.sub_right (scr_base X (by omega_using []))
  -- The prologue.
  unfold Impl.Aes.RISCV64.ctr32BsWith
  refine WP.seq ?_
  repeat rw [WP.block_append_iff (M := isa)]
  refine roundSb_wp fun s₁z b₁z o₁z m₁z rd₁z wr₁z sp₁z => ?_
  obtain hscr₁z : Scr s₁z X 2048 := ⟨by rw [wr₁z]; exact hwS, b₁z⟩
  refine bsSave_wp hscr₁z b₁z fun s₁ ov fsv vsv rdv wrv spv => ?_
  obtain o₁ : ∀ r, r ≠ sb → s₁.gpr r = s₀.gpr r := fun r h => (ov r).trans (o₁z r h)
  obtain hb₁ : s₁.gpr sb = b := (ov sb).trans b₁z
  obtain rd₁ : s₁.rd = s₀.rd := rdv.trans rd₁z
  obtain wr₁ : s₁.wr = s₀.wr := wrv.trans wr₁z
  obtain f0s : Frame [⟨b + BitVec.ofNat 64 (8 * 62), 8⟩] s₀.mem s₁.mem := fun x hx =>
    (fsv x hx).trans (congrFun m₁z x)
  obtain hscr₁ : Scr s₁ X 2048 := ⟨by rw [wr₁]; exact hwS, hb₁⟩
  obtain hvs : s₁.mem.readW (raSlotAddr b) 64 = s₀.gpr .ra := vsv.trans (o₁z _ (by decide))
  -- The slot of our return address is apart from the scratch buffer's other parts.
  obtain dV : ∀ {x lx}, (x + lx ≤ 8 * 62 ∨ 8 * 62 + 8 ≤ x) → x + lx ≤ 2040 →
      Region.Disjoint ⟨b + BitVec.ofNat 64 (8 * 62), 8⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ :=
    fun h1 h2 => Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
  rw [saveRegs_eq]
  refine Spill.save_ok (rest := []) hscr₁.al savedOffs_ho (fun p hp => ⟨_, hscr₁.wr,
    hscr₁.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) (WP.block_nil ?_)
  generalize hS : ({ s₁ with mem := Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs } : State) = s₁'
  obtain g₁' : s₁'.gpr = s₁.gpr := by rw [← hS]
  obtain mm₁ : s₁'.mem = Spill.saveMem s₁.mem (s₁.gpr sb) s₁.gpr savedOffs := by rw [← hS]
  obtain rd₁' : s₁'.rd = s₁.rd := by rw [← hS]
  obtain wr₁' : s₁'.wr = s₁.wr := by rw [← hS]
  obtain sv₁ : Spill.Saved b s₁.gpr savedOffs s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_saved savedOffs_fits _ _ _
  obtain f₁ : Frame [⟨b + BitVec.ofNat 64 320, 96⟩] s₁.mem s₁'.mem := by
    rw [mm₁, ← hb₁]; exact Spill.saveMem_frame savedOffs_range (by decide) _ _ _
  obtain hscr₁' : Scr s₁' X 2048 := ⟨by rw [wr₁']; exact hscr₁.wr, by rw [g₁']; exact hscr₁.base⟩
  refine WP.mono (maskInit_ok hscr₁') fun s₂ ⟨mk₂, fm₂, g₂, rd₂, wr₂, sp₂⟩ => ?_
  obtain b₁' : s₁'.gpr sb = b := by rw [g₁']; exact hb₁
  rw [b₁'] at mk₂ fm₂
  obtain hb₂ : s₂.gpr sb = b := by rw [g₂ _ (by decide) (by decide)]; exact b₁'
  obtain hscr₂ : Scr s₂ X 2048 := ⟨by rw [wr₂]; exact hscr₁'.wr, hb₂⟩
  obtain k₂ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ sb → s₂.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 => by rw [g₂ r h0 h1, g₁', o₁ r h2]
  refine ctrSetup_wp (ctr := ctr) hscr₂ hb₂ (k₂ _ (by decide) (by decide) (by decide))
    (by rw [wr₂, wr₁', wr₁]; exact hwC) fun s₃ m₃ o₃ rd₃ wr₃ sp₃ => ?_
  obtain k₃ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ sb → s₃.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 => by rw [o₃ r h0 h1 h2, k₂ r h0 h1 h3]
  refine shr3_wp (n := n) (by omega_arith)
    (by rw [k₃ _ (by decide) (by decide) (by decide) (by decide)]; simp [n]) fun s₄ o₄ m₄ rd₄ wr₄ sp₄ ev₄ => ?_
  obtain k₄ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ sb → s₄.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 => by rw [o₄ r h0, k₃ r h0 h1 h2 h3]
  obtain hb₄ : s₄.gpr sb = b := by
    rw [o₄ sb (by decide), o₃ _ (by decide) (by decide) (by decide)]
    exact hb₂
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, rd₁', rd₁]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, wr₁', wr₁]
  obtain hscr₄ : Scr s₄ X 2048 := ⟨by rw [wr₄']; exact hwS, hb₄⟩
  obtain fS : Frame [⟨b + BitVec.ofNat 64 (8 * 59), 24⟩, ⟨ctr, 16⟩] s₂.mem s₄.mem := by
    rw [m₄, m₃]; exact setup_frame dCb
  -- The memory so far changed only in the scratch buffer and the counter.
  obtain f₀₄ : Frame [⟨X, 2048⟩, ⟨ctr, 16⟩] s₀.mem s₄.mem := by
    obtain f01 : Frame [⟨X, 2048⟩, ⟨ctr, 16⟩] s₀.mem s₁'.mem := fun x hx =>
      ((f₁.sub fun r hr => ⟨⟨X, 2048⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega_using [])⟩) x hx).trans
        ((f0s.sub fun r hr => ⟨⟨X, 2048⟩, by simp, by
          simp only [List.mem_singleton] at hr; subst hr; exact scr_part X (by omega_using [])⟩) x hx)
    refine (f01.trans (fm₂.sub fun r hr => ⟨⟨X, 2048⟩, by simp, ?_⟩)).trans (fS.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact scr_part X (by omega_using [])
      · exact scr_part X (by omega_using [])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨X, 2048⟩, by simp, scr_part X (by omega_using [])⟩
      · exact ⟨⟨ctr, 16⟩, by simp, fun _ h => h⟩
  obtain mk₄ : MasksAt s₄.mem b allKs := by
    refine masks_frame fS (fun r hr => ?_) mk₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using []),
        Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])⟩
    · exact ⟨(dCb.sub_right (Offset.sub_base b (by omega_using []))).symm,
        (dCb.sub_right (Offset.sub_base b (by omega_using []))).symm⟩
  obtain ⟨sl₁, sl₂, sl₃⟩ := setup_slots (m := s₂.mem) (N := s₂.gpr .a4) dCb
  rw [← m₃] at sl₁ sl₂ sl₃
  -- The counter's bytes in `s₂`, as on entry.
  obtain dc : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 320, 96⟩ : Region)],
      Region.Disjoint ⟨ctr + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).sub_left (Offset.sub_base _ h)
  obtain dcm : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region),
      ⟨b + BitVec.ofNat 64 512, 96⟩], Region.Disjoint ⟨ctr + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).sub_left (Offset.sub_base _ h)
    · exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).sub_left (Offset.sub_base _ h)
  obtain dv : ∀ {x lx}, x + lx ≤ 16 → ∀ r ∈ [(⟨b + BitVec.ofNat 64 (8 * 62), 8⟩ : Region)],
      Region.Disjoint ⟨ctr + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).sub_left (Offset.sub_base _ h)
  obtain m02 : ∀ {x lx}, x + lx ≤ 16 → lx ≤ 8 →
      s₂.mem.readW (ctr + BitVec.ofNat 64 x) (8 * lx) =
        s₀.mem.readW (ctr + BitVec.ofNat 64 x) (8 * lx) := by
    intro x lx h hl
    rw [fm₂.readW (Region.contains_self _ _) (by simpa using dcm h) (by omega_using [h]),
      f₁.readW (Region.contains_self _ _) (by simpa using dc h) (by omega_using [h]),
      f0s.readW (Region.contains_self _ _) (by simpa using dv h) (by omega_using [h])]
  obtain clo₄ : cloW s₄.mem b = s₀.mem.readW ctr 64 := by
    rw [m₄, sl₁]
    simpa using m02 (x := 0) (lx := 8) (by omega_using []) (by omega_using [])
  obtain chi₄ : chiLo s₄.mem b = s₀.mem.readW (ctr + BitVec.ofNat 64 8) 32 := by
    rw [m₄, sl₂]
    exact m02 (x := 8) (lx := 4) (by omega_using []) (by omega_using [])
  obtain num₄ : numW s₄.mem b = (byteRev32 (s₀.mem.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 := by
    rw [m₄, sl₃, m02 (x := 12) (lx := 4) (by omega_using []) (by omega_using [])]
  let icb := Spec.Gcm.blockAt s₀.mem ctr
  obtain a0₄ : s₄.gpr .a0 = BK :=
    k₄ _ (by decide) (by decide) (by decide) (by decide)
  obtain a3₄ : s₄.gpr .a3 = D :=
    k₄ _ (by decide) (by decide) (by decide) (by decide)
  obtain a4₄ : s₄.gpr .a4 = s₀.gpr .a4 :=
    k₄ _ (by decide) (by decide) (by decide) (by decide)
  -- The round keys.
  obtain kc : KeysIn ⟨BK, 960⟩ BK R := fun j hj k hk => by
    rw [wordAddr, Offset.add_add]
    exact Offset.contains_base BK (by omega_arith) (by omega_arith)
  have kat₄ : KeysAt s₄.mem BK R w := keysAt_frameK f₀₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dKS
      · exact dKC) kc hp.kw
  have kd : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨BK, 960⟩ r := fun r hr => by
    simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact dKS.sub_right (scr_base X (by omega_using []))
    · exact dKS.sub_right (scr_part X (by omega_using []))
    · exact dKD
  obtain lo₄ : ∀ i < 8, ∀ j < 8, (cloW s₄.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j) :=
    fun i hi j hj => by
      rw [clo₄, readW_bit _ _ hi hj, ← BitVec.add_zero ctr, blockAt_bit _ _ (by omega_arith) hj]
      simp
  obtain hi₄ : ∀ i < 4, ∀ j < 8, (chiLo s₄.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j) :=
    fun i hi j hj => by
      rw [chi₄, readW32_bit _ _ hi hj, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega_arith,
        blockAt_bit _ _ (by omega_arith) hj, BitVec.ofNat_add, ← BitVec.add_assoc]
  -- The data is as on entry.
  obtain dd : ∀ r ∈ [(⟨X, 2048⟩ : Region), ⟨ctr, 16⟩], Region.Disjoint ⟨D, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dDS
    · exact dCD.symm
  obtain dds : ∀ r ∈ [(⟨X, 2048⟩ : Region), ⟨ctr, 16⟩], Region.Disjoint ⟨S, 16 * n⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.sS
    · exact hp.sC
  obtain data₄ : DataInv s₀.mem s₄.mem S D n 0 (keyStream R w icb) :=
    dataInv_frame f₀₄ dd dds n16 (dataInv_zero _ _ _ _ _)
  -- Our return address, in its slot.
  obtain slot₄ : s₄.mem.readW (raSlotAddr b) 64 = s₁.mem.readW (raSlotAddr b) 64 := by
    rw [fS.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dV (by omega_using []) (by omega_using [])
        · exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).symm) (by decide),
      fm₂.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dV (by omega_using []) (by omega_using [])
        · exact dV (by omega_using []) (by omega_using [])) (by decide),
      f₁.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dV (by omega_using []) (by omega_using [])) (by decide)]
  refine WP.seq (WP.mono (Q := fun (s₇ : State) => s₇.gpr sb = b ∧ s₇.wr = s₄.wr ∧
      Frame (⟨b + BitVec.ofNat 64 1024, 960⟩ :: gRegions b D n) s₄.mem s₇.mem ∧
      DataInv s₀.mem s₇.mem S D n n (keyStream R w icb)) ?_ fun s₇ ⟨base₇, wr₇, fr₇, data₇⟩ => ?_)
  · refine WP.ite (decide (8 ≤ n)) ev₄ (fun h8 => ?_) (fun _ => ?_)
    · -- Eight blocks or more, with the round keys of `encrypt4`.
      have hn8 : 8 ≤ n := by simpa using h8
      refine WP.seq (bsConvSetup_wp (R := R) (by
          rw [k₄ _ (by decide) (by decide) (by decide) (by decide)]; simp [R]) hR14
        fun s₅ ld₅ a0₅ a2₅ a1₅ o₅ m₅ rd₅ wr₅ sp₅ => ?_)
      obtain hb₅ : s₅.gpr sb = b := by
        rw [o₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hb₄
      obtain hscr₅ : Scr s₅ X 2048 := ⟨by rw [wr₅]; exact hscr₄.wr, hb₅⟩
      obtain hk : CSetup s₅ X b BK R w :=
        { scr := hscr₅
          base := hb₅
          masks := by rw [m₅]; exact mk₄
          key := List.mem_append_left _ (by rw [rd₅, rd₄']; exact hp.keys)
          kal := hp.kal
          sep := dKS
          rounds := hR14
          keys := by rw [m₅]; exact kat₄ }
      refine WP.seq (WP.mono (bsConvLoop_ok hk
        { hj := Nat.le_refl _
          a1 := a1₅
          a0 := by rw [a0₅, a0₄]
          a2 := by rw [a2₅, hb₄]; simp [keyAddr]
          rd := rfl
          wr := rfl
          sp := rfl
          keep := fun _ _ => rfl
          frame := Frame.refl _ _
          done := fun i h1 h2 => absurd h2 (by omega_arith) }) fun s₆ d₆ => ?_)
      unfold keyDone
      refine WP.seq ?_
      rw [List.singleton_append]
      refine wp_addi (imm := 64) (by decide) fun s₆' u₆ =>
        srcLoad_wp (o := o) (s := s₆') fun s₇ ld₇ ok₇ mem₇ rd₇ wr₇ sp₇ => ?_
      obtain g₇ : ∀ r ∈ [Reg.ra, .a3, .a4, .a5], s₇.gpr r = s₅.gpr r := fun r hr => by
        rw [ok₇ r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
          u₆.other r (by simp at hr; rcases hr with rfl | rfl | rfl | rfl <;> decide),
          d₆.keep r (not_ctr_writes r hr)]
      obtain a3₇ : s₇.gpr .a3 = D := by
        rw [g₇ _ (by simp), o₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), a3₄]
      obtain a4₇ : s₇.gpr .a4 = s₀.gpr .a4 := by
        rw [g₇ _ (by simp), o₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), a4₄]
      obtain hb₇ : s₇.gpr sb = b := by rw [show sb = .a5 from rfl, g₇ _ (by simp)]; exact hb₅
      obtain wr₇' : s₇.wr = s₄.wr := by rw [wr₇, u₆.wr, d₆.wr, wr₅]
      obtain rd₇' : s₇.rd = s₄.rd := by rw [rd₇, u₆.rd, d₆.rd, rd₅]
      obtain fK : Frame (kRegions b) s₄.mem s₇.mem := by rw [mem₇, u₆.mem, ← m₅]; exact d₆.frame
      obtain kdj : ∀ {x lx}, 320 ≤ x → x + lx ≤ 1024 → ∀ r ∈ kRegions b,
          Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
        intro x lx h1 h2 r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint_base _ h1 (by omega_arith)
        · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      obtain kX : ∀ r ∈ kRegions b, Region.Sub r ⟨X, 2048⟩ := frame_regions hscr₄ hb₄
      obtain K0 : s₇.gpr .a0 = b + BitVec.ofNat 64 (1920 - 64 * R) := by
        rw [ok₇ _ (by decide), u₆.gpr, d₆.a2]; exact BitVec.sub_add_cancel _ _
      obtain hg : GSetup s₇ X b S D n R w icb :=
        { scr := ⟨by rw [wr₇']; exact hscr₄.wr, hb₇⟩
          base := hb₇
          masks := masks_kept fK mk₄
          dat := by rw [wr₇', wr₄']; exact hwD
          src := by rw [rd₇', rd₄', wr₇', wr₄']; exact hp.src
          alias := hp.alias
          hn := n16
          sep := dDS
          ssep := hp.sS
          rounds := hR
          keys := fun j hj => by
            rw [mem₇, u₆.mem]
            have e : b + BitVec.ofNat 64 (1920 - 64 * R) + BitVec.ofNat 64 (64 * j) = keyAddr b R j := by
              rw [Offset.add_add, keyAddr]; congr 2; omega_arith
            rw [e]; exact d₆.keys j hj
          lo := by
            rw [show cloW s₇.mem b = cloW s₄.mem b from
              fK.readW (Region.contains_self _ _) (kdj (by omega_using []) (by omega_using [])) (by decide)]
            exact lo₄
          hi := by
            rw [show chiLo s₇.mem b = chiLo s₄.mem b from
              fK.readW (Region.contains_self _ _) (kdj (by omega_using []) (by omega_using [])) (by decide)]
            exact hi₄ }
      obtain hs₇ := hg.toK K0
      obtain hsr : s₇.gpr (srcReg o) = S := by
        cases o with
        | false => exact a3₇.trans (hp.inPlace rfl).symm
        | true =>
          show s₇.gpr .a2 = S
          rw [ld₇ rfl, u₆.other _ (by decide), d₆.keep _ (by decide), ld₅ rfl,
            k₄ _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.outOf rfl
      obtain hi₇ : GInvK o s₀.mem s₇ b S D n R w icb 0 s₇ :=
        ⟨by omega_arith, by rw [a3₇]; simp, by rw [hsr]; simp, by rw [a4₇]; simp [n], hb₇, rfl,
          rfl, rfl, rfl, rfl, Frame.refl _ _, by
            rw [show numW s₇.mem b = numW s₄.mem b from
              fK.readW (Region.contains_self _ _) (kdj (by omega_using []) (by omega_using [])) (by decide),
              num₄, icb_lo]
            simp [icb],
          dataInv_frame fK (fun r hr => dDS.sub_right (kX r hr)) (fun r hr => hp.sS.sub_right (kX r hr)) n16 data₄⟩
      refine WP.mono (bsGroups_ok hs₇ a3₇ hsr hp.inPlace hi₇) fun s₈ gd => ⟨gd.base, gd.wr.trans wr₇', ?_, gd.data⟩
      refine (fK.sub fun r hr => ?_).trans (gd.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · -- Fewer, with the round keys as they are.
      refine WP.seq ?_
      rw [WP.block_append_iff (M := isa)]
      refine bsSrc_wp (o := o) fun s₅ ld₅ ok₅ mem₅ rd₅ wr₅ sp₅ => ?_
      refine bsKb_wp (s := s₅) (R := R)
        (by rw [ok₅ _ (by decide), k₄ _ (by decide) (by decide) (by decide) (by decide)]; simp [R])
        hR14 fun s₆ kb₆ o₆ m₆ rd₆ wr₆ sp₆ => ?_
      obtain k₆ : ∀ r, r ≠ t0 → r ≠ .ra → r ≠ .a2 → s₆.gpr r = s₄.gpr r :=
        fun r h0 h4 h5 => by rw [o₆ r h0 h4, ok₅ r h5]
      obtain hb₆ : s₆.gpr sb = b := by rw [k₆ _ (by decide) (by decide) (by decide)]; exact hb₄
      obtain rd₆' : s₆.rd = s₄.rd := by rw [rd₆, rd₅]
      obtain wr₆' : s₆.wr = s₄.wr := by rw [wr₆, wr₅]
      obtain m₆' : s₆.mem = s₄.mem := by rw [m₆, mem₅]
      obtain a0₆ : s₆.gpr .a0 = BK := by rw [k₆ _ (by decide) (by decide) (by decide), a0₄]
      obtain a3₆ : s₆.gpr .a3 = D := by rw [k₆ _ (by decide) (by decide) (by decide), a3₄]
      obtain a4₆ : s₆.gpr .a4 = s₀.gpr .a4 := by rw [k₆ _ (by decide) (by decide) (by decide), a4₄]
      obtain hs : GSetupK (encrypt4K .ra) s₆ X b S D n R w icb :=
        { scr := ⟨by rw [wr₆']; exact hscr₄.wr, hb₆⟩
          base := hb₆
          masks := by rw [m₆']; exact mk₄
          dat := by rw [wr₆', wr₄']; exact hwD
          src := by rw [rd₆', rd₄', wr₆', wr₄']; exact hp.src
          alias := hp.alias
          hn := n16
          sep := dDS
          ssep := hp.sS
          crypt_ok := fun s₁ scr hb mk ha hra hrd hwr hf _ hin => encrypt4K_ok (K := ⟨BK, 960⟩)
            { scr := scr
              masks := mk
              rounds := hR
              kbr := by decide
              k0 := by rw [ha, hra, ← kb₆, a0₆, ok₅ _ (by decide), a0₄]
              kin := fun j hj k hk => ⟨_, List.mem_append_left _ (by rw [hrd, rd₆', rd₄']; exact hp.keys),
                by rw [ha, a0₆]; exact kc j hj k hk⟩
              kal := by rw [ha, a0₆]; exact hp.kal
              kat := by rw [ha, a0₆]; exact kc
              kd := by rw [hb]; exact kd _ (by simp [gRegions])
              keys := by rw [ha, a0₆]; exact keysAt_frameK hf kd kc (by rw [m₆']; exact kat₄) } hin
          lo := by rw [m₆']; exact lo₄
          hi := by rw [m₆']; exact hi₄ }
      obtain hsr : s₆.gpr (srcReg o) = S := by
        cases o with
        | false => exact a3₆.trans (hp.inPlace rfl).symm
        | true =>
          show s₆.gpr .a2 = S
          rw [o₆ _ (by decide) (by decide), ld₅ rfl, k₄ _ (by decide) (by decide) (by decide) (by decide)]
          exact hp.outOf rfl
      refine WP.mono (Q := GDone s₀.mem s₆ b S D n R w icb) ?_ fun s₇ gd => ⟨gd.base, gd.wr.trans wr₆',
        by rw [← m₆']; exact gd.frame.mono fun r hr => List.mem_cons_of_mem _ hr, gd.data⟩
      refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
        (by rw [a4₆]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
      · have hn0 : n = 0 := by simpa using h0
        exact WP.block_nil ⟨hb₆, rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩
      · have hn0 : n ≠ 0 := by simpa using h0
        exact bsGroups_ok hs a3₆ hsr hp.inPlace
          ⟨by omega_arith, by rw [a3₆]; simp, by rw [hsr]; simp, by rw [a4₆]; simp [n], hb₆, rfl,
            rfl, rfl, rfl, rfl, Frame.refl _ _, by rw [m₆', num₄, icb_lo]; simp [icb], by rw [m₆']; exact data₄⟩
  -- Nothing after the prologue writes the slots below the masks or our return address's.
  obtain slotD : ∀ {x lx}, 320 ≤ x → x + lx ≤ 8 * 59 ∨ 8 * 62 ≤ x → x + lx ≤ 1024 →
      ∀ r ∈ (⟨b + BitVec.ofNat 64 1024, 960⟩ : Region) :: gRegions b D n,
        Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
    intro x lx h1 h2 h3 r hr
    simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint_base b (by omega_arith) (by omega_arith)
    · exact Offset.disjoint b (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (dDS.sub_right (scr_part X (by omega_arith))).symm
  -- The epilogue.
  obtain sv : Spill.Saved b s₁.gpr savedOffs s₇.mem := by
    obtain dS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
      · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
    obtain dS2 : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (8 * 59), 24⟩ : Region), ⟨ctr, 16⟩],
        Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint b (by omega_using []) (by omega_using []) (by omega_using [])
      · exact (dCb.sub_right (Offset.sub_base b (by omega_using []))).symm
    obtain dG := slotD (x := 320) (lx := 96) (by omega_using []) (by omega_using []) (by omega_using [])
    exact ((sv₁.frame_in savedOffs_range fm₂ dS).frame_in savedOffs_range fS dS2).frame_in
      savedOffs_range fr₇ dG
  obtain hscr₇ : Scr s₇ X 2048 := ⟨by rw [wr₇, wr₄']; exact hwS, by rw [base₇]⟩
  rw [WP.block_append_iff (M := isa), restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₁]; exact hscr₁.al) base₇ savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₇.wr, by
      rw [← base₇]
      exact hscr₇.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) sv)
    fun s₈ rs₈ => ?_
  obtain hb₈ : s₈.gpr sb = b := by rw [rs₈.other sb (by decide), base₇]
  refine srcRestore_wp (o := true) (X := X) ⟨by rw [rs₈.wr]; exact hscr₇.wr, hb₈⟩ hb₈
    fun s₉ ok₉ ra₉ mem₉ => ?_
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    obtain h1 : r ≠ sb := by revert hr; revert r; decide
    obtain h2 : r ≠ .ra := by revert hr; revert r; decide
    rw [ok₉ r h2, rs₈.gpr_of (.inl hr'), o₁ r h1]
  · rw [ra₉, ite_eq_left rfl, rs₈.mem, fr₇.readW (Region.contains_self _ _)
      (slotD (x := 8 * 62) (lx := 8) (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), slot₄, hvs]
  · show Spec.Gcm.blocksAt s₉.mem D n = _
    rw [mem₉, rs₈.mem]
    exact ctr32_of_dataInv data₇
  · show Spec.Gcm.blockAt s₉.mem ctr = _
    rw [mem₉, rs₈.mem]
    refine ctr_after fun k hk => ?_
    obtain hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨ctr, 16⟩ r) →
        m' (ctr + BitVec.ofNat 64 k) = m (ctr + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC fr₇ (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dCb.sub_right (Offset.sub_base b (by omega_using []))
        · exact dCb.sub_right (Region.sub_prefix (by omega_using []))
        · exact dCb.sub_right (Offset.sub_base b (by omega_using []))
        · exact dCD),
      m₄, m₃, setup_ctr dCb hk, m02 (x := 12) (lx := 4) (by omega_using []) (by omega_using [])]
    obtain e7 : BitVec.ofNat 64 (s₀.gpr .a4).toNat = s₂.gpr .a4 := by
      rw [k₂ _ (by decide) (by decide) (by decide)]; simp
    split
    · have dcS : ∀ r ∈ [(⟨b + BitVec.ofNat 64 320, 96⟩ : Region)], Region.Disjoint ⟨ctr, 16⟩ r :=
        fun r hr => by simpa using dc (x := 0) (lx := 16) (by omega_using []) r hr
      obtain dcM : ∀ r ∈ [(⟨b + BitVec.ofNat 64 416, 48⟩ : Region), ⟨b + BitVec.ofNat 64 512, 96⟩],
          Region.Disjoint ⟨ctr, 16⟩ r :=
        fun r hr => by simpa using dcm (x := 0) (lx := 16) (by omega_using []) r hr
      obtain dcV : ∀ r ∈ [(⟨b + BitVec.ofNat 64 (8 * 62), 8⟩ : Region)], Region.Disjoint ⟨ctr, 16⟩ r :=
        fun r hr => by simpa using dv (x := 0) (lx := 16) (by omega_using []) r hr
      rw [fm₂.bytes (R := ⟨ctr, 16⟩) dcM (by simp) hk, f₁.bytes (R := ⟨ctr, 16⟩) dcS (by simp) hk,
        f0s.bytes (R := ⟨ctr, 16⟩) dcV (by simp) hk]
    · rw [e7]

/-- In place. -/
theorem correctBs {s₀ : State} (hp : Proof.Aes.ctr32BsRISCV64.pre s₀) :
    WP isa Impl.Aes.RISCV64.ctr32Bs s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        Proof.Aes.ctr32BsRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, -, hR, hal, w, hw⟩ := hp
  obtain hwD : (⟨s₀.gpr .a3, 16 * (s₀.gpr .a4).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (correctBsWith (o := false) (S := s₀.gpr .a3) (w := w)
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, hwD, by rw [hwr]; simp, List.mem_append_right _ hwD,
      fun h => absurd h (by decide), fun _ => rfl, dKC, dKD, dKS, dCD, dCS, dDS, dCD.symm, dDS, .inl rfl,
      hR, hal, hw⟩) fun s' ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, fun w' hw' => ⟨?_, h₄⟩⟩
  rw [h₃, aesWith_congr hw hw']

/-- Out of place. -/
theorem correctBsTo {s₀ : State} (hp : Proof.Aes.ctr32BsToRISCV64.pre s₀) :
    WP isa Impl.Aes.RISCV64.ctr32BsTo s₀ fun s' =>
      (∀ r ∈ RISCV64.preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
        Proof.Aes.ctr32BsToRISCV64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKC, dKD, dKS, dCD, dCS, dDS, sC, sD, sS, -, -, hR, hal, w, hw⟩ := hp
  refine WP.mono (correctBsWith (o := true) (S := s₀.gpr .a6) (w := w)
    ⟨by rw [hrd]; simp, by rw [hwr]; simp, by rw [hwr]; simp, by rw [hwr]; simp,
      List.mem_append_left _ (by rw [hrd]; simp), fun _ => rfl, fun h => absurd h (by decide),
      dKC, dKD, dKS, dCD, dCS, dDS, sC, sS, sD, hR, hal, hw⟩)
    fun s' ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, fun w' hw' => ⟨?_, h₄⟩⟩
  rw [h₃, aesWith_congr hw hw']

theorem ctr32Bs_correct (s : State) (hs : Proof.Aes.ctr32BsRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Aes.RISCV64.ctr32Bs s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32BsRISCV64.post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correctBs hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

theorem ctr32BsTo_correct (s : State) (hs : Proof.Aes.ctr32BsToRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Aes.RISCV64.ctr32BsTo s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32BsToRISCV64.post s s' := by
  obtain ⟨t, s', he, h₁, hra, h₂⟩ := correctBsTo hs
  exact ⟨t, s', he, ⟨h₁, Exec.sp he, hra⟩, h₂⟩

end VG.Proof.Aes.RISCV64
