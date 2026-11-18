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

The proof is `Ctr32.lean`'s without the key loop: the prologue is the same
but for our return address, which is saved, and `ra`, which `encrypt4K .ra`
compares with the round key pointer (`bsKb_wp`), and the groups are
`groupsK_ok` with the round keys outside the scratch buffer.
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
    rw [← h j hj 0 (by decide) i hi, h' j hj 0 (by decide) i hi])]

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
write `counter`, `dst` and `scratch`. `src` overlaps none of the regions it
may write, and neither `src` nor `dst` wraps around the end of the address
space. The pointers, `rounds` and `n` are public; the round keys, the
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
    src.Disjoint counter ∧ src.Disjoint data ∧ src.Disjoint scratch ∧
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
  refine bsSrc_wp (o := o) fun s₃' ld₃ ok₃ mem₃ rd₃' wr₃' sp₃' => ?_
  refine bsKb_wp (s := s₃') (R := R)
    (by rw [ok₃ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide)]; simp [R])
    hR14 fun s₄ kb₄ o₄ m₄ rd₄ wr₄ sp₄ => ?_
  obtain k₄ : ∀ r, r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ sb → r ≠ .ra → r ≠ .a2 → s₄.gpr r = s₀.gpr r :=
    fun r h0 h1 h2 h3 h4 h5 => by rw [o₄ r h0 h4, ok₃ r h5, k₃ r h0 h1 h2 h3]
  obtain hb₄ : s₄.gpr sb = b := by
    rw [o₄ sb (by decide) (by decide), ok₃ sb (by decide), o₃ _ (by decide) (by decide) (by decide)]
    exact hb₂
  obtain rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃', rd₃, rd₂, rd₁', rd₁]
  obtain wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃', wr₃, wr₂, wr₁', wr₁]
  obtain hscr₄ : Scr s₄ X 2048 := ⟨by rw [wr₄']; exact hwS, hb₄⟩
  obtain fS : Frame [⟨b + BitVec.ofNat 64 (8 * 59), 24⟩, ⟨ctr, 16⟩] s₂.mem s₄.mem := by
    rw [m₄, mem₃, m₃]; exact setup_frame dCb
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
    rw [m₄, mem₃, sl₁]
    simpa using m02 (x := 0) (lx := 8) (by omega_using []) (by omega_using [])
  obtain chi₄ : chiLo s₄.mem b = s₀.mem.readW (ctr + BitVec.ofNat 64 8) 32 := by
    rw [m₄, mem₃, sl₂]
    exact m02 (x := 8) (lx := 4) (by omega_using []) (by omega_using [])
  obtain num₄ : numW s₄.mem b = (byteRev32 (s₀.mem.readW (ctr + BitVec.ofNat 64 12) 32)).setWidth 64 := by
    rw [m₄, mem₃, sl₃, m02 (x := 12) (lx := 4) (by omega_using []) (by omega_using [])]
  let icb := Spec.Gcm.blockAt s₀.mem ctr
  obtain a0₄ : s₄.gpr .a0 = BK :=
    k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain a3₄ : s₄.gpr .a3 = D :=
    k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain a4₄ : s₄.gpr .a4 = s₀.gpr .a4 :=
    k₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- The round keys.
  obtain kc : KeysIn ⟨BK, 960⟩ BK R := fun j hj k hk => by
    rw [wordAddr, Offset.add_add]
    exact Offset.contains_base BK (by omega_arith) (by omega_arith)
  obtain hs : GSetupK s₄ X b S D .ra ⟨BK, 960⟩ BK n R w icb :=
    { scr := hscr₄
      base := hb₄
      masks := mk₄
      dat := by rw [wr₄']; exact hwD
      src := by rw [rd₄', wr₄']; exact hp.src
      alias := hp.alias
      hn := n16
      sep := dDS
      ssep := hp.sS
      rounds := hR
      kbr := by decide
      k0 := by
        rw [← kb₄, ok₃ _ (by decide), k₃ _ (by decide) (by decide) (by decide) (by decide)]
      kin := fun j hj k hk => ⟨_, List.mem_append_left _ (by rw [rd₄']; exact hp.keys), kc j hj k hk⟩
      kal := hp.kal
      kat := kc
      kd := fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dKS.sub_right (scr_base X (by omega_using []))
        · exact dKS.sub_right (scr_part X (by omega_using []))
        · exact dKD
      keys := keysAt_frameK f₀₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dKS
          · exact dKC) kc hp.kw
      lo := fun i hi j hj => by
        rw [clo₄, readW_bit _ _ hi hj, ← BitVec.add_zero ctr,
          blockAt_bit _ _ (by omega_arith) hj]
        simp
      hi := fun i hi j hj => by
        rw [chi₄, readW32_bit _ _ hi hj, show 8 * (7 - i) + j = 8 * (15 - (8 + i)) + j by omega_arith,
          blockAt_bit _ _ (by omega_arith) hj, BitVec.ofNat_add, ← BitVec.add_assoc] }
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
  -- The source, in `a2` out of place.
  obtain hsr : s₄.gpr (srcReg o) = S := by
    cases o with
    | false => exact a3₄.trans (hp.inPlace rfl).symm
    | true =>
      show s₄.gpr .a2 = S
      rw [o₄ _ (by decide) (by decide), ld₃ rfl, k₃ _ (by decide) (by decide) (by decide) (by decide)]
      exact hp.outOf rfl
  refine WP.seq (WP.mono (Q := GDone s₀.mem s₄ b S D n R w icb) ?_ fun s₇ gd => ?_)
  · refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ (by omega_arith)
      (by rw [a4₄]; simp [n])) (fun h0 => ?_) (fun h0 => ?_)
    · have hn0 : n = 0 := by simpa using h0
      exact WP.block_nil ⟨hb₄, rfl, rfl, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (by omega_arith)⟩
    · have hn0 : n ≠ 0 := by simpa using h0
      obtain hi₄ : GInvK o s₀.mem s₄ b S D .ra BK n R w icb 0 s₄ :=
        ⟨by omega_arith, by rw [a3₄]; simp, by rw [hsr]; simp, by rw [a4₄]; simp [n], hb₄, a0₄, rfl,
          rfl, rfl, rfl, rfl, Frame.refl _ _, by rw [num₄, icb_lo]; simp [icb], data₄⟩
      -- By doublewords if the data's addresses are aligned.
      unfold ctrGroupsK
      refine WP.seq (alignTest_wp a3₄ hsr hp.inPlace fun s₇ v u₇ ev => ?_)
      obtain hi₇ := hi₄.of_t0 (by decide) u₇
      exact WP.ite _ ev
        (fun h => groupsK_ok hs (fun _ => by simpa using h) hi₇)
        (fun _ => groupsK_ok hs (fun h => Bool.noConfusion h) hi₇)
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
    obtain dG : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 320, 96⟩ r :=
      hs.slot_disj (by omega_using []) (by omega_using []) (by omega_using [])
    exact ((sv₁.frame_in savedOffs_range fm₂ dS).frame_in savedOffs_range fS dS2).frame_in
      savedOffs_range gd.frame dG
  obtain hscr₇ : Scr s₇ X 2048 := ⟨by rw [gd.wr, wr₄']; exact hwS, by rw [gd.base]⟩
  rw [WP.block_append_iff (M := isa), restoreRegs_eq]
  refine WP.mono (Spill.restore_wp (B := b) (by rw [← hb₁]; exact hscr₁.al) gd.base savedOffs_ho
    savedOffs_restorable (fun p hp => ⟨_, List.mem_append_right _ hscr₇.wr, by
      rw [← gd.base]
      exact hscr₇.contains (by have := savedOffs_range p hp; omega_using [this]) (by decide)⟩) sv)
    fun s₈ rs₈ => ?_
  obtain hb₈ : s₈.gpr sb = b := by rw [rs₈.other sb (by decide), gd.base]
  refine srcRestore_wp (o := true) (X := X) ⟨by rw [rs₈.wr]; exact hscr₇.wr, hb₈⟩ hb₈
    fun s₉ ok₉ ra₉ mem₉ => ?_
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have hr' : r ∈ savedOffs.map Prod.fst := by rw [savedOffs_regs]; exact hr
    obtain h1 : r ≠ sb := by revert hr; revert r; decide
    obtain h2 : r ≠ .ra := by revert hr; revert r; decide
    rw [ok₉ r h2, rs₈.gpr_of (.inl hr'), o₁ r h1]
  · rw [ra₉, ite_eq_left rfl, rs₈.mem, gd.frame.readW (Region.contains_self _ _)
      (hs.slot_disj (x := 8 * 62) (lx := 8) (by omega_using []) (by omega_using []) (by omega_using []))
      (by decide), slot₄, hvs]
  · show Spec.Gcm.blocksAt s₉.mem D n = _
    rw [mem₉, rs₈.mem]
    exact ctr32_of_dataInv gd.data
  · show Spec.Gcm.blockAt s₉.mem ctr = _
    rw [mem₉, rs₈.mem]
    refine ctr_after fun k hk => ?_
    obtain hC : ∀ {m m' : Mem} {rs : List Region}, Frame rs m m' →
        (∀ r ∈ rs, Region.Disjoint ⟨ctr, 16⟩ r) →
        m' (ctr + BitVec.ofNat 64 k) = m (ctr + BitVec.ofNat 64 k) :=
      fun hf hd => hf.bytes hd (by simp) hk
    rw [hC gd.frame (fun r hr => by
        simp only [gRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dCb.sub_right (Region.sub_prefix (by omega_using []))
        · exact dCb.sub_right (Offset.sub_base b (by omega_using []))
        · exact dCD),
      m₄, mem₃, m₃, setup_ctr dCb hk, m02 (x := 12) (lx := 4) (by omega_using []) (by omega_using [])]
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
      dKC, dKD, dKS, dCD, dCS, dDS, sC, sS, .inr sD, hR, hal, hw⟩)
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
