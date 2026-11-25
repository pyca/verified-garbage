module

public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Ctr
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Aes.X86_64.Ctr32
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Spec.Gcm.Contract

/-!
# Bitsliced AES counter mode on x86-64: the whole function

`vg_aes_ctr32` and its out-of-place form `vg_aes_ctr32_to`, by one proof: the
source is at `rcx` and the output at `r11`, the same in place. The batches'
loop (`loop_ok`) starts from round keys in slices (`Ready`) and leaves them,
so the keyed functions of AES-CMAC use it too.
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize,
counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64;
256])`: XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, nor the return
address on the stack, and `data` may not wrap around the end of the address
space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n` are public;
the key schedule, the counter block and the data are secret. -/
def ctr32X86_64 : Contract X86_64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let counter : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scratch : Region := ⟨s.gpr .r9, 2048⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .rsi).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (16 * ((s.gpr .rsi).toNat + 1)))
    blocksAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .rdx)) (blocksAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 (s.gpr .r8).toNat (blockAt s.mem (s.gpr .rdx))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

open VG.X86_64 in
/-- `ctr32X86_64` with only the scratch buffer the bitsliced implementation
needs, 1480 bytes (it uses the first 1376). A caller of that implementation
alone sets aside a smaller buffer. -/
def ctr32X86_64S : Contract X86_64.isa :=
  { ctr32X86_64 with
    pre := fun s =>
      let sched : Region := ⟨s.gpr .rdi, 240⟩
      let counter : Region := ⟨s.gpr .rdx, 16⟩
      let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
      let scratch : Region := ⟨s.gpr .r9, 1480⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
      sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
      counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
      ret.Disjoint counter ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
      (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) }

open VG.X86_64 in
/-- X86-64 contract for `vg_aes_expand_key(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other, and the writable ones may not
overlap the return address on the stack. `key_len` is 16, 24 or 32. The
pointers and `key_len` are public; the key is secret. -/
def expandKeyX86_64 : Contract X86_64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let sched : Region := ⟨s.gpr .rdx, 240⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ret.Disjoint sched ∧ ret.Disjoint scratch ∧
    ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) (16 * (Spec.Aes.rounds ((s.gpr .rsi).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Aes

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Aes.X86_64 VG.Impl.Aes.X86_64.Sse VG.Proof.Aes VG.Proof.Aes.X86_64.Sse
open VG.Proof.Aes.Memory (Processed)
open VG.Spec.Gcm (blockAt inc32 toBytes Block)

/-! ## The counter block's bytes -/

/-- The counter, as `bswap32` gives it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := Sse.icb_lo m ctr

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (bswap32 (bswap32 (m.readW (ctr + BitVec.ofNat 64 12) 32) +
        (BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [Sse.icb_lo, show (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n by
      apply BitVec.eq_of_toNat_eq; simp]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', bswap32_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

/-! ## The loop over batches -/

/-- The registers the loop writes are not these. -/
abbrev CKept (x : Reg) : Prop :=
  x ≠ .rax ∧ x ≠ .rcx ∧ x ≠ .rdi ∧ x ≠ .r8 ∧ x ≠ .r10 ∧ x ≠ .r11

/-- Block `i` of the keystream. -/
def ksBlock (nr : Nat) (w : List Byte) (icb : Block) (i : Nat) : Spec.Aes.State :=
  Spec.Aes.cipher nr w (ctrState icb i)

/-- Block `i` of the output. -/
def outBlock (nr : Nat) (w : List Byte) (icb : Block) (m₀ : Mem) (X : Addr) (i : Nat) : Spec.Aes.State :=
  Vector.ofFn fun x => (ksBlock nr w icb i).getD x 0 ^^^ m₀ (X + BitVec.ofNat 64 (16 * i + x))

/-- The arguments of a run over `n` blocks from `X` to `D`, with the counter block at `C`. -/
structure LP (b C X D : Addr) (n nr : Nat) (s₀ : State) : Prop where
  n16 : 16 * n < 2 ^ 64
  inD : ⟨D, 16 * n⟩ ∈ s₀.wr
  inX : ⟨X, 16 * n⟩ ∈ s₀.rd ++ s₀.wr
  inC : ⟨C, 16⟩ ∈ s₀.wr
  dDS : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 1480⟩
  dXS : Region.Disjoint ⟨X, 16 * n⟩ ⟨b, 1480⟩
  dCS : Region.Disjoint ⟨C, 16⟩ ⟨b, 1480⟩
  dCD : Region.Disjoint ⟨C, 16⟩ ⟨D, 16 * n⟩
  dCX : Region.Disjoint ⟨C, 16⟩ ⟨X, 16 * n⟩
  mode : Mode X D n
  rsi : s₀.gpr .rsi = BitVec.ofNat 64 nr
  rdx : s₀.gpr .rdx = C
  r9 : s₀.gpr .r9 = b

/-- What the loop writes. -/
abbrev lR (b C D : Addr) (n : Nat) : List Region := [⟨D, 16 * n⟩, ⟨C, 16⟩, ⟨b, 1480⟩]

/-- After `k` blocks. -/
structure LI (s₀ : State) (b C X D : Addr) (n nr : Nat) (w : List Byte) (icb : Block) (k : Nat) (s : State) : Prop where
  ready : Ready b nr w s.mem s.rd s.wr
  rcx : s.gpr .rcx = X + BitVec.ofNat 64 (16 * k)
  r11 : s.gpr .r11 = D + BitVec.ofNat 64 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - k)
  gpr : ∀ x, CKept x → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (lR b C D n) s₀.mem s.mem
  ctr : blockAt s.mem C = Nat.repeat inc32 k icb
  done : Processed s₀.mem s.mem D n k (outBlock nr w icb s₀.mem X)

variable {s₀ : State} {b C X D : Addr} {n nr : Nat} {w : List Byte} {icb : Block}

theorem blockAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨C, 16⟩ r) :
    blockAt m' C = blockAt m C :=
  block_ext fun k hk => by
    rw [toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk]
    exact hf.bytes (R := ⟨C, 16⟩) hd (show (16 : Nat) ≤ 2 ^ 64 by decide) hk

/-- The source past the blocks done is as it was. -/
theorem LI.src (hp : LP b C X D n nr s₀) {k : Nat} {s : State} (h : LI s₀ b C X D n nr w icb k s) {i : Nat}
    (hi : i < 16 * n) (hk : 16 * k ≤ i) : s.mem (X + BitVec.ofNat 64 i) = s₀.mem (X + BitVec.ofNat 64 i) := by
  have hn := hp.n16
  rcases hp.mode with e | hd
  · rw [e, h.done i hi, ite_eq_right (by omega)]
  · refine h.frame.bytes (R := ⟨X, 16 * n⟩) (fun r hr => ?_) (show 16 * n ≤ 2 ^ 64 by omega) hi
    simp only [lR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hd
    · exact hp.dCX.symm
    · exact hp.dXS

theorem ctrBatch_ok (hp : LP b C X D n nr s₀) {k : Nat} (hk : k < n) {s : State} (h : LI s₀ b C X D n nr w icb k s) :
    WP isa ctrBatch s fun s' => ∃ t, 0 < t ∧ k + t ≤ n ∧ LI s₀ b C X D n nr w icb (k + t) s' ∧
      X86_64.eval .ne s' = some (decide (n - (k + t) ≠ 0)) := by
  have hn := hp.n16
  obtain ⟨t, ht⟩ : ∃ t, t = min 8 (n - k) := ⟨_, rfl⟩
  have ht8 : t ≤ 8 := by omega
  have ht0 : 0 < t := by omega
  have hkt : k + t ≤ n := by omega
  have r9 : s.gpr .r9 = b := by rw [h.gpr _ (by decide), hp.r9]
  have rdx : s.gpr .rdx = C := by rw [h.gpr _ (by decide), hp.rdx]
  have inC : ⟨C, 16⟩ ∈ s.wr := by rw [h.wr]; exact hp.inC
  have hbuf : ∀ i < 8, InRegions s.wr (bufAddr b i) 16 := fun i hi => h.ready.bufIn hi
  refine WP.seq (WP.mono (ctrBlocks_ok r9 rdx ⟨_, List.mem_append_right _ inC, Region.contains_self _ _⟩
    ⟨_, List.mem_append_right _ inC, Offset.contains_base _ (by decide) (by decide)⟩ hbuf) fun s1 h1 => ?_)
  have hr1 : Ready b nr w s1.mem s1.rd s1.wr := by
    rw [h1.rd, h1.wr]
    refine h.ready.frame h1.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨Offset.disjoint _ (.inr (by decide)) (by decide) (by decide),
      Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)⟩
  have buf1 : BufIs s1.mem b fun i => ctrState icb (k + i) := fun i hi x hx => by
    rw [h1.ctr i hi x hx, h.ctr, rep_add]
    simp only [ctrState]
    rw [getD_ofFn _ hx]
  refine WP.seq (WP.mono (encrypt8_ok ⟨hr1, h1.r9, by rw [h1.gpr _ (by decide) (by decide), h.gpr _ (by decide), hp.rsi], buf1⟩)
    fun s2 h2 => ?_)
  have g2 : ∀ x, x ≠ .rax → x ≠ .r10 → s2.gpr x = s.gpr x := fun x a c => by rw [h2.gpr x a c, h1.gpr x a c]
  have r82 : s2.gpr .r8 = BitVec.ofNat 64 (n - k) := by rw [g2 _ (by decide) (by decide), h.r8]
  refine WP.seq (WP.mono (batchSize_ok (r := n - k) (by omega) r82) fun s3 ⟨rdi3, r103, rax3, g3, m3, rd3, wr3, _⟩ => ?_)
  rw [← ht] at rdi3 r103
  have f3 : Frame [⟨b, 1480⟩] s.mem s3.mem := by
    rw [m3]
    exact (h1.frame.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by rw [List.mem_singleton.mp hr]; exact bufR_sub b⟩).trans
      (h2.frame.sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by rw [List.mem_singleton.mp hr]; exact low416_sub b⟩)
  have rd3' : s3.rd = s.rd := rd3.trans (h2.rd.trans h1.rd)
  have wr3' : s3.wr = s.wr := wr3.trans (h2.wr.trans h1.wr)
  have hx3 : XP s3 s₀.mem b X D n k t (outBlock nr w icb s₀.mem X) (ksBlock nr w icb) := by
    refine ⟨ht8, hkt, hn, by rw [wr3', h.wr]; exact hp.inD, by rw [rd3', wr3', h.rd, h.wr]; exact hp.inX,
      fun i hi => by rw [wr3']; exact hbuf i hi, (hp.dDS.sub_right (bufR_sub b)).symm, hp.mode, fun i hi hik => ?_,
      fun i hi x hx => ?_, fun i hi x hx => ?_⟩
    · rw [← h.src hp hi hik]
      exact f3.bytes (R := ⟨X, 16 * n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dXS)
        (show 16 * n ≤ 2 ^ 64 by omega) hi
    · rw [m3, h2.buf i (by omega) x hx]; rfl
    · rw [outBlock, getD_ofFn _ hx]
  refine WP.seq (WP.mono (xor_loop hx3 ht0 (s := s3) ⟨?_, ?_, ?_, ?_, fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, ?_⟩)
    fun s4 h4 => ?_)
  · rw [g3 _ (by decide) (by decide) (by decide), g2 _ (by decide) (by decide), h.rcx]; rfl
  · rw [g3 _ (by decide) (by decide) (by decide), g2 _ (by decide) (by decide), h.r11]; rfl
  · rw [rax3, g2 _ (by decide) (by decide), r9, bufAddr_eq]
  · rw [r103]; rfl
  · exact h.done.frame f3 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dDS) (by omega)
  have g4 : ∀ x, CKept x ∨ x = .r8 → s4.gpr x = s.gpr x := by
    intro x hx
    have hx' : x ≠ .rax ∧ x ≠ .rcx ∧ x ≠ .rdi ∧ x ≠ .r10 ∧ x ≠ .r11 := by
      rcases hx with hx | rfl
      · exact ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2⟩
      · decide
    rw [h4.gpr x hx'.1 hx'.2.2.2.1 hx'.2.1 hx'.2.2.2.2, g3 x hx'.1 hx'.2.2.2.1 hx'.2.2.1, g2 x hx'.1 hx'.2.2.2.1]
  have f4 : Frame [⟨D, 16 * n⟩, ⟨b, 1480⟩] s.mem s4.mem :=
    (f3.mono fun r hr => List.mem_cons_of_mem _ hr).trans (h4.frame.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_self)
  have hc4 : blockAt s4.mem C = blockAt s.mem C := blockAt_frame f4 fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.dCD
    · exact hp.dCS
  have hr3 : Ready b nr w s3.mem s3.rd s3.wr := by rw [m3, rd3, wr3]; exact h2.ready
  have hr4 : Ready b nr w s4.mem s4.rd s4.wr := by
    rw [h4.rd, h4.wr]
    refine hr3.frame h4.frame fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨(hp.dDS.sub_right (sub_scratch b (by decide))).symm, (hp.dDS.sub_right (sub_scratch b (by decide))).symm⟩
  refine WP.mono (ctrNext_ok (C := C) (t := t) (r := n - (k + t)) ?_ ?_ ?_ (by omega) ?_)
    fun s5 ⟨c5, f5, r85, g5, rd5, wr5, z5⟩ => ⟨t, ht0, hkt, ⟨?_, ?_, ?_, r85, fun x hx => ?_, ?_, ?_, ?_, ?_, ?_⟩, z5⟩
  · rw [g4 _ (.inl (by decide)), rdx]
  · rw [h4.gpr _ (by decide) (by decide) (by decide) (by decide), rdi3]
  · rw [g4 _ (.inr rfl), h.r8]; congr 1; omega
  · rw [h4.wr, wr3']; exact inC
  · rw [rd5, wr5]
    refine hr4.frame f5 fun r hr => ?_
    rw [List.mem_singleton.mp hr]
    exact ⟨(hp.dCS.sub_right (sub_scratch b (by decide))).symm, (hp.dCS.sub_right (sub_scratch b (by decide))).symm⟩
  · rw [g5 _ (by decide) (by decide), h4.rcx]
  · rw [g5 _ (by decide) (by decide), h4.r11]
  · rw [g5 x hx.1 hx.2.2.2.1, g4 x (.inl hx), h.gpr x hx]
  · exact rd5.trans (h4.rd.trans (rd3'.trans h.rd))
  · exact wr5.trans (h4.wr.trans (wr3'.trans h.wr))
  · refine h.frame.trans ((f4.sub fun r hr => ?_).trans (f5.mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), fun _ h => h⟩
  · rw [c5, hc4, h.ctr, rep_add]
  · exact h4.done.frame f5 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dCD.symm) (by omega)

theorem loop_ok (hp : LP b C X D n nr s₀) (h0 : n ≠ 0) {s : State} (h : LI s₀ b C X D n nr w icb 0 s) :
    WP isa ctrLoop s (LI s₀ b C X D n nr w icb n) := by
  let I : Nat → State → Prop := fun c s => ∃ k, c = n - k ∧ k < n ∧ LI s₀ b C X D n nr w icb k s
  refine WP.loop (M := isa) I ?_ n s ⟨0, rfl, by omega, h⟩
  rintro c' s' ⟨k, rfl, hk, hs'⟩
  refine WP.mono (ctrBatch_ok hp hk hs') fun s4 ⟨t, ht0, hkt, h4, hz⟩ => ?_
  by_cases hl : n - (k + t) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show k + t = n by omega] at h4
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, k + t, rfl, by omega, h4⟩

/-- The output is the counter mode of the source. -/
theorem ctr32_of_processed {m₀ m : Mem} (h : Processed m₀ m D n n (outBlock nr w icb m₀ X)) :
    Spec.Gcm.blocksAt m D n = Spec.Gcm.ctr32 (Spec.Gcm.aesWith nr w) icb (Spec.Gcm.blocksAt m₀ X n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk, BitVec.add_assoc,
    ← BitVec.ofNat_add, h _ (by omega), ite_eq_left (by omega), show (16 * i + k) / 16 = i by omega,
    show (16 * i + k) % 16 = k by omega, outBlock, getD_ofFn _ hk, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine (BitVec.xor_comm _ _).trans (congrArg (m₀ (X + BitVec.ofNat 64 (16 * i + k)) ^^^ ·) ?_)
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, ksBlock, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some, getD_eq _ hk]
  rfl

/-! ## The whole function -/

/-- The output: the data in place, `r11` out of place. -/
def dOut (to : Bool) (s : State) : Addr := if to then s.gpr .r11 else s.gpr .rcx

/-- What both contracts give: the source (`rcx`) and the output (`dOut`), the
same in place, disjoint out of place, and the other buffers. -/
structure CPre (to : Bool) (s₀ : State) : Prop where
  hwC : (⟨s₀.gpr .rdx, 16⟩ : Region) ∈ s₀.wr
  hwD : (⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.wr
  hwS : (⟨s₀.gpr .r9, 2048⟩ : Region) ∈ s₀.wr ∨ (⟨s₀.gpr .r9, 1480⟩ : Region) ∈ s₀.wr
  hrS : (⟨s₀.gpr .rdi, 240⟩ : Region) ∈ s₀.rd
  hsrc : (⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩ : Region) ∈ s₀.rd ++ s₀.wr
  dSS : Region.Disjoint ⟨s₀.gpr .rdi, 240⟩ ⟨s₀.gpr .r9, 1480⟩
  dCS : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨s₀.gpr .r9, 1480⟩
  dCD : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩
  dCX : Region.Disjoint ⟨s₀.gpr .rdx, 16⟩ ⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩
  dDS : Region.Disjoint ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩ ⟨s₀.gpr .r9, 1480⟩
  dXS : Region.Disjoint ⟨s₀.gpr .rcx, 16 * (s₀.gpr .r8).toNat⟩ ⟨s₀.gpr .r9, 1480⟩
  dRC : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdx, 16⟩
  dRD : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨dOut to s₀, 16 * (s₀.gpr .r8).toNat⟩
  dRS : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .r9, 1480⟩
  mode : Mode (s₀.gpr .rcx) (dOut to s₀) (s₀.gpr .r8).toNat
  hR : (s₀.gpr .rsi).toNat = 10 ∨ (s₀.gpr .rsi).toNat = 12 ∨ (s₀.gpr .rsi).toNat = 14

/-- `16 n` bytes disjoint from a 16-byte region fit in the address space. -/
theorem n16_of_disj {C X : Addr} {n : Nat} (h : Region.Disjoint ⟨C, 16⟩ ⟨X, 16 * n⟩) : 16 * n < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hc => h C (by simp [Region.Contains]) ?_
  simp only [Region.Contains]
  have := (C - X).isLt
  omega

/-- What is disjoint from the scratch buffer is disjoint from its first 1480 bytes. -/
theorem scr_pre {r : Region} {b : Addr} (h : r.Disjoint ⟨b, 2048⟩) : r.Disjoint ⟨b, 1480⟩ :=
  h.sub_right (Region.sub_prefix (by decide))

theorem CPre.of {s₀ : State} (hp : Proof.Aes.ctr32X86_64.pre s₀) : CPre false s₀ := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, dRC, dRD, dRS, -, hR⟩ := hp
  exact
  { hwC := by rw [hwr]; simp, hwD := by rw [hwr]; simp [dOut]
    hwS := .inl (by rw [hwr]; simp)
    hrS := by rw [hrd]; simp, hsrc := by rw [hwr]; simp, dSS := scr_pre dSS, dCS := scr_pre dCS
    dCD, dCX := dCD, dDS := scr_pre dDS, dXS := scr_pre dDS, dRC, dRD, dRS := scr_pre dRS
    mode := .inl rfl, hR }

theorem CPre.ofS {s₀ : State} (hp : Proof.Aes.ctr32X86_64S.pre s₀) : CPre false s₀ := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCD, dCS, dDS, dRC, dRD, dRS, -, hR⟩ := hp
  exact
  { hwC := by rw [hwr]; simp, hwD := by rw [hwr]; simp [dOut]
    hwS := .inr (by rw [hwr]; simp)
    hrS := by rw [hrd]; simp, hsrc := by rw [hwr]; simp, dSS, dCS
    dCD, dCX := dCD, dDS, dXS := dDS, dRC, dRD, dRS
    mode := .inl rfl, hR }

theorem CPre.ofTo {s₀ : State} (hp : AesNi.ctr32ToX86_64.pre s₀) : CPre true s₀ := by
  obtain ⟨hrd, hwr, dSC, dSD, dSS, dCX, dCD, dCS, dXD, dXS, dDS, dRC, dRD, dRS, -, -, hR⟩ := hp
  exact { hwC := by rw [hwr]; simp, hwD := by rw [hwr]; simp [dOut]
          hwS := .inl (by rw [hwr]; simp)
          hrS := by rw [hrd]; simp, hsrc := by rw [hrd]; simp, dSS := scr_pre dSS
          dCS := scr_pre dCS, dCD, dCX, dDS := scr_pre dDS
          dXS := scr_pre dXS, dRC, dRD, dRS := scr_pre dRS, mode := dXD, hR }

/-- What the code ensures, in place or out of place. -/
def CPost (to : Bool) (s₀ s' : State) : Prop :=
  Spec.Gcm.blocksAt s'.mem (dOut to s₀) (s₀.gpr .r8).toNat =
      Spec.Gcm.ctr32 (Spec.Gcm.aesWith (s₀.gpr .rsi).toNat
        (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * ((s₀.gpr .rsi).toNat + 1))))
        (Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx)) (Spec.Gcm.blocksAt s₀.mem (s₀.gpr .rcx) (s₀.gpr .r8).toNat) ∧
    Spec.Gcm.blockAt s'.mem (s₀.gpr .rdx) =
      Nat.repeat Spec.Gcm.inc32 (s₀.gpr .r8).toNat (Spec.Gcm.blockAt s₀.mem (s₀.gpr .rdx))

/-- The entry: the output's pointer in `r11`, and whether there are blocks. -/
theorem entry_ok (to : Bool) (s : State) :
    WP isa (.block ((if to then [] else [.mov .r11 (.reg .rcx)]) ++ ([.alu .test .r8 (.reg .r8)] : List Instr))) s fun s' =>
      s'.gpr .r11 = dOut to s ∧ (∀ x, x ≠ .r11 → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.gpr .r8 == 0) := by
  apply WP.of_runBlock
  cases to
  · simp only [Bool.false_eq_true, ite_false, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa,
      reduceExec, execAlu, readSrc, Option.map_some, Option.bind_some, gpr_setReg, reduceCtorEq, BitVec.and_self,
      Option.some.injEq, exists_eq_left', gpr_arithFlags, zf_arithFlags]
    exact ⟨rfl, fun x hx => by simp only [hx, ite_false], rfl, rfl, rfl, trivial⟩
  · simp only [ite_true, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, isa,
      reduceExec, execAlu, readSrc, Option.bind_some, BitVec.and_self,
      Option.some.injEq, exists_eq_left', gpr_arithFlags, zf_arithFlags]
    exact ⟨rfl, fun x _ => trivial, rfl, rfl, rfl, trivial⟩

/-- `CPre`'s facts for the loop, in a state with the same arguments. -/
theorem CPre.lp {to : Bool} {s₀ : State} (hp : CPre to s₀) :
    LP (s₀.gpr .r9) (s₀.gpr .rdx) (s₀.gpr .rcx) (dOut to s₀) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₀ :=
  ⟨n16_of_disj hp.dCD, hp.hwD, hp.hsrc, hp.hwC, hp.dDS, hp.dXS, hp.dCS, hp.dCD, hp.dCX, hp.mode, by simp, rfl, rfl⟩

/-- From the loop's end to the contract's. -/
theorem CPre.post {to : Bool} {s₀ s' : State} (hp : CPre to s₀) (hg : ∀ x, CKept x → s'.gpr x = s₀.gpr x)
    (hf : Frame (lR (s₀.gpr .r9) (s₀.gpr .rdx) (dOut to s₀) (s₀.gpr .r8).toNat) s₀.mem s'.mem)
    (hc : blockAt s'.mem (s₀.gpr .rdx) = Nat.repeat inc32 (s₀.gpr .r8).toNat (blockAt s₀.mem (s₀.gpr .rdx)))
    (hd : Processed s₀.mem s'.mem (dOut to s₀) (s₀.gpr .r8).toNat (s₀.gpr .r8).toNat
      (outBlock (s₀.gpr .rsi).toNat (Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) (16 * ((s₀.gpr .rsi).toNat + 1)))
        (blockAt s₀.mem (s₀.gpr .rdx)) s₀.mem (s₀.gpr .rcx))) : gprPreserved s₀ s' ∧ CPost to s₀ s' := by
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, ctr32_of_processed hd, hc⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · refine hf.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [lR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dRD
    · exact hp.dRC
    · exact hp.dRS

theorem correct (to : Bool) {s₀ : State} (hp : CPre to s₀) :
    WP isa (ctr32G to) s₀ fun s' => gprPreserved s₀ s' ∧ CPost to s₀ s' := by
  have hlp := hp.lp
  have hn := hlp.n16
  refine WP.seq (WP.mono (entry_ok to s₀) fun s1 ⟨r11, g1, m1, rd1, wr1, z1⟩ => ?_)
  refine WP.ite (s₀.gpr .r8 == 0) (by simp [X86_64.eval, z1]) (fun h0 => ?_) (fun h0 => ?_)
  · have h0 : (s₀.gpr .r8).toNat = 0 := by rw [eq_of_beq h0]; rfl
    refine WP.block_nil (hp.post (fun x hx => g1 x hx.2.2.2.2.2) (by rw [m1]; exact Frame.refl _ _) ?_ ?_)
    · rw [m1, h0]; rfl
    · rw [m1]; intro i hi; omega
  have h0 : (s₀.gpr .r8).toNat ≠ 0 := fun h => by
    rw [beq_eq_false_iff_ne] at h0
    exact h0 (BitVec.eq_of_toNat_eq h)
  have hkp : KPre (s₀.gpr .r9) (s₀.gpr .rdi) (s₀.gpr .rsi).toNat s1 := by
    refine ⟨g1 _ (by decide), g1 _ (by decide), by rw [g1 _ (by decide)]; simp, hp.hR, ?_, ?_, hp.dSS⟩
    · rw [wr1]; exact hp.hwS
    · rw [rd1]; exact hp.hrS
  refine WP.seq (WP.mono (keys_ok hkp) fun s2 h2 => ?_)
  have f2 : Frame [⟨s₀.gpr .r9, 1480⟩] s₀.mem s2.mem := by rw [← m1]; exact h2.frame
  have g2 : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → x ≠ .r11 → s2.gpr x = s₀.gpr x := fun x a c d e => by
    rw [h2.gpr x a c d, g1 x e]
  refine WP.mono (loop_ok (icb := blockAt s₀.mem (s₀.gpr .rdx)) hlp h0 (s := s2) ?_) fun s3 h3 =>
    hp.post h3.gpr h3.frame h3.ctr h3.done
  have hr2 := h2.ready
  rw [m1] at hr2
  refine ⟨hr2, ?_, ?_, ?_, fun x hx => g2 x hx.1 hx.2.2.2.2.1 hx.2.2.1 hx.2.2.2.2.2, h2.rd.trans rd1, h2.wr.trans wr1,
    f2.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), ?_, ?_⟩
  · rw [g2 _ (by decide) (by decide) (by decide) (by decide)]; simp
  · rw [h2.gpr _ (by decide) (by decide) (by decide), r11]; simp
  · rw [g2 _ (by decide) (by decide) (by decide) (by decide)]; simp
  · exact blockAt_frame f2 fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dCS
  · exact (Processed.refl s₀.mem _ _ _).frame f2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.dDS) (by omega)

theorem ctr32_correct (s : State) (hs : Proof.Aes.ctr32X86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct false (CPre.of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem ctr32To_correct (s : State) (hs : AesNi.ctr32ToX86_64.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.ctr32To s t s' ∧ abiPreserved s s' ∧ AesNi.ctr32ToX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct true (CPre.ofTo hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- `vg_aes_ctr32` against `ctr32X86_64S`, with the scratch buffer it uses. -/
theorem ctr32S_correct (s : State) (hs : Proof.Aes.ctr32X86_64S.pre s) :
    ∃ t s', Exec isa Impl.Aes.X86_64.ctr32 s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.ctr32X86_64S.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct false (CPre.ofS hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

/-- The analysis needs nothing of the regions, so the code is constant-time
under any precondition. -/
theorem ctr32_ctP {P : State → Prop} : ConstantTime isa P Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.ctr32 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem ctr32_ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.ctr32 := ctr32_ctP

theorem ctr32S_ct : ConstantTime isa Proof.Aes.ctr32X86_64S.pre Proof.Aes.ctr32X86_64S.pub
    Impl.Aes.X86_64.ctr32 := ctr32_ctP

theorem ctr32To_ct : ConstantTime isa AesNi.ctr32ToX86_64.pre AesNi.ctr32ToX86_64.pub Impl.Aes.X86_64.ctr32To := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .r11])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.X86_64
