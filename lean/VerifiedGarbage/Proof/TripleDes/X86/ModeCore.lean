import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
import VerifiedGarbage.Proof.Modes.X86.Core
import VerifiedGarbage.Impl.TripleDes.X86.Modes
import VerifiedGarbage.Spec.TripleDes.Cbc
import VerifiedGarbage.Proof.TripleDes.ModeCipher

/-!
# Triple DES's core for the modes on x86 (32-bit)

`dirCoreSpec d`: Triple DES's core for the direction `d`
(`Impl.TripleDes.X86.dirCore d`) meets what the modes need of a core
(`Proof.Modes.X86.CoreSpec`), with the key a schedule, read through the
first stack argument, its cipher `Spec.TripleDes.cipher` for encryption and
`Spec.TripleDes.invCipher` for decryption, and the key ready when the copy of
the schedule in the core's slots is the key. The block function's call
(`cryptCall_ok`) is ECB's (`Ecb.call_ok`) with its arguments in other
registers.
-/

namespace VG.Proof.TripleDes.X86.Mode

open VG VG.X86 VG.X86.Wp VG.Impl.TripleDes.X86
open VG.Impl.Modes.X86 (sb at_ argOp slotAt)
open VG.Proof.Modes.X86 (coreRegion blkRegion blkAddr stkRegion slotA CoreSpec Layout ScrIn write4_apply)
open VG.Spec.Aes (bytesAt)
open VG.Spec.TripleDes (Direction)
open VG.Proof.TripleDes (dirCipher dirBlock bytesAt_eq dirCipher_bytes scheduleAt_copy scheduleAt_eq_of_frame)
open VG.Proof.Rc2.X86 (addr32)

/-! ## The schedule's copy -/

/-- `W` words from `[ecx + 4 w]` to slot `k + w`. -/
def copyCode (k W : Nat) : List Instr :=
  (List.range W).flatMap fun w => [.mov .eax (.mem (at_ .ecx (4 * w))), .store (slotAt (k + w)) .eax]

theorem copyCode_succ (k W : Nat) :
    copyCode k (W + 1) = copyCode k W ++
      ([.mov .eax (.mem (at_ .ecx (4 * W))), .store (slotAt (k + W)) .eax] : List Instr) := by
  simp [copyCode, List.range_succ]

theorem copyCode_wp {k : Nat} : ∀ (W : Nat) {s : State} {P B : BitVec 32}, s.gpr .ecx = P → s.gpr .edi = B →
    P.toNat + 4 * W ≤ 2 ^ 32 → B.toNat + 4 * (k + W) ≤ 2 ^ 32 →
    (∀ w < W, InRegions (s.rd ++ s.wr) (addr P (4 * w)) 4) → (∀ w < W, InRegions s.wr (addr B (4 * (k + w))) 4) →
    Region.Disjoint ⟨P.setWidth 64, 4 * W⟩ ⟨slotA B k, 4 * W⟩ → ∀ {is : List Instr} {Q : State → Prop},
    (∀ s', (∀ i < 4 * W, s'.mem (slotA B k + BitVec.ofNat 64 i) = s.mem (P.setWidth 64 + BitVec.ofNat 64 i)) →
      Frame [⟨slotA B k, 4 * W⟩] s.mem s'.mem → (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) →
    WP isa (.block (copyCode k W ++ is)) s Q
  | 0, s, _, _, _, _, _, _, _, _, _, _, _, k' => by
    simpa [copyCode] using k' s (fun i hi => by omega) (Frame.refl _ _) (fun _ _ => rfl) rfl rfl
  | W + 1, s, P, B, hc, hd, hP, hB, hr, hw, hdis, is, Q, k' => by
    rw [copyCode_succ, List.append_assoc]
    have hdis' : Region.Disjoint ⟨P.setWidth 64, 4 * W⟩ ⟨slotA B k, 4 * W⟩ :=
      (hdis.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
    refine copyCode_wp W hc hd (by omega) (by omega) (fun w hw' => hr w (by omega)) (fun w hw' => hw w (by omega))
      hdis' fun s₁ m₁ f₁ g₁ rd₁ wr₁ => ?_
    simp only [List.cons_append]
    have hin : InRegions (s₁.rd ++ s₁.wr) (addr P (4 * W)) 4 := by rw [rd₁, wr₁]; exact hr W (by omega)
    refine wp_ldm (by rw [g₁ _ (by decide)]; exact hc) hin fun s₂ u₂ => ?_
    refine wp_stm (B := B) (by rw [u₂.other _ (by decide), g₁ _ (by decide)]; exact hd)
      (by rw [u₂.wr, wr₁]; exact hw W (by omega)) fun s₃ u₃ => ?_
    have eP : addr P (4 * W) = P.setWidth 64 + BitVec.ofNat 64 (4 * W) := addr_eq (by omega)
    have eB : addr B (4 * (k + W)) = slotA B k + BitVec.ofNat 64 (4 * W) := by
      rw [addr_eq (by omega), VG.Offset.add_add, Nat.mul_add]
    have m₃ : s₃.mem = s₁.mem.writeW (slotA B k + BitVec.ofNat 64 (4 * W))
        (s₁.mem.readW (P.setWidth 64 + BitVec.ofNat 64 (4 * W)) 32) := by
      rw [u₃.mem, u₂.mem, u₂.gpr, eP, eB]
    -- The new word's source is not among the copies so far.
    have src₁ : ∀ t < 4, s₁.mem (P.setWidth 64 + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 t) =
        s.mem (P.setWidth 64 + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 t) := fun t ht => by
      rw [VG.Offset.add_add]
      exact f₁.bytes (R := ⟨P.setWidth 64, 4 * (W + 1)⟩) (fun r hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact hdis.sub_right (Region.sub_prefix (by omega))) (by show 4 * (W + 1) ≤ 2 ^ 64; omega)
        (by show 4 * W + t < 4 * (W + 1); omega)
    refine k' s₃ (fun i hi => ?_) ?_ (fun r hr' => by rw [u₃.gpr, u₂.other r hr', g₁ r hr'])
      (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁])
    · rw [m₃, write4_apply]
      by_cases h : i < 4 * W
      · rw [ite_eq_right (fun h' => ?_), m₁ i h]
        have := (VG.Offset.lt_iff (slotA B k + BitVec.ofNat 64 i) (slotA B k) (d := 4 * W) (n := 4) (by omega)).mp h'
        rw [VG.Proof.Modes.X86.sub_self_add _ (by omega)] at this
        omega
      · have e : slotA B k + BitVec.ofNat 64 i = slotA B k + BitVec.ofNat 64 (4 * W) + BitVec.ofNat 64 (i - 4 * W) := by
          rw [VG.Offset.add_add (slotA B k) (4 * W) (i - 4 * W), Nat.add_sub_cancel' (by omega)]
        rw [e, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          ite_eq_left (by omega), ← Mem.readW_byte _ _ (by omega), src₁ _ (by omega), VG.Offset.add_add,
          Nat.add_sub_cancel' (by omega)]
    · rw [m₃]
      have hc4 : (⟨slotA B k, 4 * (W + 1)⟩ : Region).Contains (slotA B k + BitVec.ofNat 64 (4 * W)) (32 / 8) :=
        VG.Offset.contains_base _ (by omega) (by omega)
      exact (f₁.sub fun r hr' => ⟨⟨slotA B k, 4 * (W + 1)⟩, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr'; subst hr'; exact Region.sub_prefix (by omega)⟩).writeW
        (List.mem_singleton_self _) _ hc4

/-! ## The key -/

/-- The schedule, at the address in the first stack argument, and that
argument, outside the regions `rs`, as is the core's stack. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.TripleDes.Schedule) : Prop :=
  ∃ p : BitVec 32, InRegions (s.rd ++ s.wr) (s.ea (argOp 0)) 4 ∧ s.mem.readW (s.ea (argOp 0)) 32 = p ∧
    k = Spec.TripleDes.scheduleAt s.mem (p.setWidth 64) ∧ (⟨p.setWidth 64, 384⟩ : Region) ∈ s.rd ++ s.wr ∧
    p.toNat + 384 ≤ 2 ^ 32 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p.setWidth 64, 384⟩ r) ∧
    (∀ r ∈ rs, Region.Disjoint ⟨s.ea (argOp 0), 4⟩ r) ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .esp) 16) r

theorem dirCore_total (d : Direction) : (dirCore d).total = 236 := rfl

/-- The schedule's copy is `k`, the core's stack is apart from the scratch
buffer, which does not wrap around. -/
def Ready (s : State) (B : BitVec 32) (k : Spec.TripleDes.Schedule) : Prop :=
  Spec.TripleDes.scheduleAt s.mem (slotA B schedSlot) = k ∧
    Region.Disjoint (stkRegion (s.gpr .esp) 16) ⟨B.setWidth 64, 4 * 236⟩ ∧ B.toNat + 4 * 236 ≤ 2 ^ 32

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.TripleDes.Schedule} (h : KeyArgs s rs k)
    (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame rs s.mem s'.mem) :
    KeyArgs s' rs k := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, hadis, hsdis⟩ := h
  have hea : s'.ea (argOp 0) = s.ea (argOp 0) := by
    show (s'.gpr .esp + _).setWidth 64 = (s.gpr .esp + _).setWidth 64; rw [hesp]
  refine ⟨p, by rw [hrd, hwr, hea]; exact hin, ?_, (scheduleAt_eq_of_frame _ hf hdis).symm,
    by rw [hrd, hwr]; exact hsch, hfit, hdis, by rw [hea]; exact hadis, by rw [hesp]; exact hsdis⟩
  rw [hea, hf.readW (Region.contains_self _ _) hadis (by decide), hp]

theorem ready_frame {d : Direction} {s s' : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule}
    {rs : List Region} (h : Ready s B k) (hesp : s'.gpr .esp = s.gpr .esp) (hf : Frame rs s.mem s'.mem)
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore d) B) r ∨ Region.Sub r (blkRegion (dirCore d) B)) :
    Ready s' B k := by
  obtain ⟨hk, hs, hfit⟩ := h
  refine ⟨?_, by rw [hesp]; exact hs, hfit⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_]
  · exact hk
  rcases hd r hr with h' | h'
  · exact h'.sub_left (VG.Offset.sub_base _ (by simp only [dirCore, schedSlot, bufSlot]; omega))
  · exact (VG.Offset.disjoint _ (.inr (by simp only [dirCore, schedSlot, bufSlot]; omega)) (by simp only [schedSlot]; omega)
      (by simp only [dirCore, bufSlot]; omega)).sub_right h'

theorem prepare_wp (d : Direction) {s : State} {B : BitVec 32} {rs : List Region} {k : Spec.TripleDes.Schedule}
    (hB : s.gpr sb = B) (hs : ScrIn s B (dirCore d).total)
    (hR : (⟨B.setWidth 64, 4 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k)
    (_ : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).prepare s fun s' => Ready s' B k ∧ s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hin, hp, rfl, hsch, hfit, hdis, -, hsdis⟩ := hk
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hsep : Region.Disjoint ⟨p.setWidth 64, 384⟩ ⟨B.setWidth 64, 4 * 236⟩ := hdis _ hR
  have hcopy : copySchedule = [.mov .ecx (.mem (argOp 0))] ++ copyCode schedSlot 96 := rfl
  show WP isa (.block copySchedule) s _
  rw [hcopy, ← List.append_nil (copyCode schedSlot 96), List.singleton_append]
  refine wp_ldm (B := s.gpr .esp) rfl hin fun s₁ u₁ => ?_
  rw [show s.mem.readW (addr (s.gpr .esp) (4 + 4 * 0)) 32 = p from hp] at u₁
  have hp64 : ∀ w < 96, addr p (4 * w) = p.setWidth 64 + BitVec.ofNat 64 (4 * w) := fun w hw => addr_eq (by omega)
  refine copyCode_wp (P := p) (B := B) 96 u₁.gpr (by rw [u₁.other _ (by decide)]; exact hB) (by omega) (by simp only [schedSlot]; omega)
    (fun w hw => ?_) (fun w hw => ?_) ?_ fun s₂ m₂ f₂ g₂ rd₂ wr₂ => WP.block_nil ?_
  · rw [u₁.rd, u₁.wr, hp64 w hw]; exact ⟨_, hsch, VG.Offset.contains_base _ (by omega) (by omega)⟩
  · rw [u₁.wr, addr_eq (by simp only [schedSlot]; omega)]
    have hc : (⟨B.setWidth 64, 4 * 236⟩ : Region).Contains
        (B.setWidth 64 + BitVec.ofNat 64 (4 * (schedSlot + w))) 4 :=
      VG.Offset.contains_base _ (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)
    have hw' := hs.wr
    rw [dirCore_total] at hw'
    exact ⟨_, hw', hc⟩
  · exact hsep.sub_right (VG.Offset.sub_base _ (by simp only [schedSlot]; omega))
  have esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [g₂ _ (by decide), u₁.other _ (by decide)]
  refine ⟨⟨?_, ?_, hfB⟩, by rw [g₂ _ (by decide), u₁.other _ (by decide)]; exact hB, esp₂,
    ?_, by rw [rd₂, u₁.rd], by rw [wr₂, u₁.wr]⟩
  · rw [scheduleAt_copy (p := p.setWidth 64) fun i hi => ?_]
    rw [m₂ i (by omega), u₁.mem]
  · rw [esp₂]; have := hsdis _ hR; rw [dirCore_total] at this; exact this
  · rw [← u₁.mem]
    exact f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega)⟩

theorem addr32_add {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) :
    addr32 (B + BitVec.ofNat 32 d) = B.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

theorem toNat_add {B : BitVec 32} {d : Nat} (h : B.toNat + d < 2 ^ 32) : (B + BitVec.ofNat 32 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 32), Nat.mod_eq_of_lt h]

/-- The block function's result, as the direction's block function. -/
theorem blockResult_eq (d : Direction) (k : Spec.TripleDes.Schedule) (b : Spec.TripleDes.Block) :
    VG.Proof.TripleDes.X86.blockResult k d b = dirBlock d k b := by cases d <;> rfl

/-! ## The block function's call -/

/-- Writing back the word read from `a` changes nothing. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  rw [write4_apply]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl

theorem cryptCall_eq (d : Direction) : cryptCall d =
    .frame (.push [.eax, .ecx, .edx])
      (.call (match d with | .encrypt => "vg_triple_des_encrypt_block" | .decrypt => "vg_triple_des_decrypt_block")
        (Ecb.blockCode d)) (.pop .eax 3) := by cases d <;> rfl

/-- The block function's arguments: the schedule at `edx`, the block at
`ecx` and the working space at `eax` (`Ecb.CallPre`, through other
registers). -/
structure CallPre (s : State) : Prop where
  reads : Covers [⟨addr32 (s.gpr .edx), 384⟩, ⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩] (s.rd ++ s.wr)
  writes : Covers [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩] s.wr
  keyScratch : (Region.mk (addr32 (s.gpr .edx)) 384).Disjoint ⟨addr32 (s.gpr .eax), 512⟩
  dataScratch : (Region.mk (addr32 (s.gpr .ecx)) 8).Disjoint ⟨addr32 (s.gpr .eax), 512⟩
  keyFit : (s.gpr .edx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .ecx).toNat + 8 ≤ 2 ^ 32
  bufFit : (s.gpr .eax).toNat + 512 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .edx), 384⟩
  stackData : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .ecx), 8⟩
  stackBuf : (below (s.gpr .esp) 16).Disjoint ⟨addr32 (s.gpr .eax), 512⟩

structure CallPost (d : Direction) (s s' : State) : Prop where
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩, below (s.gpr .esp) 16] s.mem s'.mem
  output : Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    blockResult (Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .edx))) d (Spec.TripleDes.blockAt s.mem (addr32 (s.gpr .ecx)))

theorem cryptCall_ok (d : Direction) (s : State) (hp : CallPre s) : WP isa (cryptCall d) s (CallPost d s) := by
  rw [cryptCall_eq]
  let rs : List Reg := [.eax, .ecx, .edx]
  have hrs : .esp ∉ rs := by decide
  have fit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat := hp.stackLo
  let sE := (pushed rs s).callEntry
  have a0 : arg sE 0 = s.gpr .edx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a1 : arg sE 1 = s.gpr .ecx := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have a2 : arg sE 2 = s.gpr .eax := by rw [callEntry_arg fit hrs (by decide)]; rfl
  have eA : argAddr sE 0 = ((s.gpr .esp) - BitVec.ofNat 32 12).setWidth 64 := by rw [callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = s.gpr .esp - BitVec.ofNat 32 16 := by rw [callEntry_esp']; rfl
  have b12 : Region.Sub (below (s.gpr .esp) 12) (below (s.gpr .esp) 16) := below_sub (by decide) hp.stackLo
  have r4 : Region.Sub ⟨((s.gpr .esp) - BitVec.ofNat 32 16).setWidth 64, 4⟩ (below (s.gpr .esp) 16) :=
    Region.sub_prefix (by decide)
  have hcode : Ecb.blockCode d = block d := by cases d <;> rfl
  refine VG.Proof.Rc2.X86.Cbc.callWithGpr (c := Ecb.blockCode d) (k := blockContract d)
    (by rw [hcode]; exact block_correct d) (Ecb.block_nosp d) (by decide) hrs
    (by rw [Ecb.block_stack]; exact hp.stackLo) (rd := [⟨addr32 (s.gpr .edx), 384⟩, ⟨argAddr sE 0, 12⟩])
    (wr := [⟨addr32 (s.gpr .ecx), 8⟩, ⟨addr32 (s.gpr .eax), 512⟩]) ⟨?_, ?_, ?_⟩ ?_
  · change (blockContract d).pre (sE.withRegions _ _)
    simp only [blockContract, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, eA, eSp]
    refine ⟨trivial, trivial, hp.keyScratch, hp.dataScratch, hp.stackData.sub_left b12,
      hp.stackBuf.sub_left b12, hp.stackData.sub_left r4, hp.stackBuf.sub_left r4,
      hp.keyFit, hp.dataFit, hp.bufFit, ?_⟩
    rw [sub_toNat hp.stackLo]
    have := (s.gpr .esp).isLt
    omega
  · intro a n ⟨r, hr, hc⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · apply InRegions_append_cons.mpr
      left
      rw [eA] at hc
      exact hc
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
    · exact InRegions_append_cons.mpr (.inr (hp.reads a n ⟨_, by simp, hc⟩))
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hp.writes a n h
    exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
  · intro s' rd wr cs frame ⟨s₂, mem₂, gpr₂, post⟩
    rw [Ecb.block_stack] at frame
    change (blockContract d).post (sE.withRegions _ _) s₂ at post
    simp only [blockContract, State.withRegions_mem, arg_withRegions, a0, a1, mem₂] at post
    have stackFrame := callEntry_frame fit hrs
    change Frame [below (s.gpr .esp) 16] s.mem sE.mem at stackFrame
    refine ⟨cs, rd, wr, frame, ?_⟩
    rw [post,
      VG.Proof.TripleDes.scheduleAt_eq_of_frame (p := addr32 (s.gpr .edx)) stackFrame
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackKey.symm),
      VG.Proof.TripleDes.blockAt_eq_of_frame (p := addr32 (s.gpr .ecx)) stackFrame
        (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact hp.stackData.symm)]

theorem crypt_wp (d : Direction) {s : State} {B : BitVec 32} {k : Spec.TripleDes.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready s B k) (hst : (dirCore d).stack ≤ (s.gpr .esp).toNat) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .esp = s.gpr .esp ∧ Ready s' B k ∧
      Frame [coreRegion (dirCore d) B, stkRegion (s.gpr .esp) (dirCore d).stack] s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw) =
        dirCipher d k (bytesAt s.mem (blkAddr (dirCore d) B j) (4 * (dirCore d).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hk, hstk, hfB⟩ := hr
  have hw := hs.wr
  rw [dirCore_total] at hw
  have hst' : 16 ≤ (s.gpr .esp).toNat := hst
  have hB' : s.gpr .edi = B := hB
  have slotIn : ∀ o, o + 4 ≤ 4 * 236 → (⟨B.setWidth 64, 4 * 236⟩ : Region).Contains (addr B o) 4 := fun o h => by
    rw [addr_eq (by omega)]; exact VG.Offset.contains_base _ (by omega) (by omega)
  show WP isa (.seq (.block cryptSetup) (.seq (cryptCall d) (.block cryptDone))) s _
  refine WP.seq ?_
  refine wp_ldm (b := .edi) (o := 4 * dSlot) hB' ⟨_, List.mem_append_right _ hw, slotIn _ (by simp only [dSlot, schedSlot]; omega)⟩
    fun s₁ u₁ => wp_ldm (b := .edi) (o := 4 * nSlot) ((u₁.other _ (by decide)).trans hB')
      (by rw [u₁.rd, u₁.wr]; exact ⟨_, List.mem_append_right _ hw, slotIn _ (by simp only [nSlot, schedSlot]; omega)⟩)
    fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ =>
      wp_addi fun s₇ u₇ => WP.block_nil ?_
  have edi₇ : s₇.gpr .edi = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  have esi₇ : s₇.gpr .esi = s.mem.readW (addr B (4 * dSlot)) 32 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ebp₇ : s₇.gpr .ebp = s.mem.readW (addr B (4 * nSlot)) 32 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, u₁.mem]
  have eax₇ : s₇.gpr .eax = B := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]; exact hB'
  have ecx₇ : s₇.gpr .ecx = B + BitVec.ofNat 32 512 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]; rfl
  have edx₇ : s₇.gpr .edx = B + BitVec.ofNat 32 520 := by
    rw [u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hB]; rfl
  have esp₇ : s₇.gpr .esp = s.gpr .esp := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₇ : s₇.rd = s.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₇ : s₇.wr = s.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have aK : addr32 (s₇.gpr .edx) = B.setWidth 64 + BitVec.ofNat 64 520 := by rw [edx₇]; exact addr32_add (by omega)
  have aD : addr32 (s₇.gpr .ecx) = B.setWidth 64 + BitVec.ofNat 64 512 := by rw [ecx₇]; exact addr32_add (by omega)
  have aW : addr32 (s₇.gpr .eax) = B.setWidth 64 := by rw [eax₇]; rfl
  have scrSub : ∀ (off n : Nat), off + n ≤ 4 * 236 → ∃ r' ∈ s₇.wr, ∃ o,
      (B.setWidth 64 + BitVec.ofNat 64 off) = r'.base + BitVec.ofNat 64 o ∧ o + n ≤ r'.len :=
    fun off n h => ⟨_, by rw [wr₇]; exact hw, off, rfl, h⟩
  have e0 : B.setWidth 64 = B.setWidth 64 + BitVec.ofNat 64 0 := by simp
  have hpre : CallPre s₇ := by
    refine ⟨Covers.right (Covers.of_sub fun r hr => ?_), Covers.of_sub fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [aK]; exact scrSub 520 384 (by omega)
      · rw [aD]; exact scrSub 512 8 (by omega)
      · rw [aW, e0]; exact scrSub 0 512 (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [aD]; exact scrSub 512 8 (by omega)
      · rw [aW, e0]; exact scrSub 0 512 (by omega)
    · rw [aK, aW]; exact VG.Offset.disjoint_base _ (by omega) (by omega)
    · rw [aD, aW]; exact VG.Offset.disjoint_base _ (by omega) (by omega)
    · rw [edx₇, toNat_add (by omega)]; omega
    · rw [ecx₇, toNat_add (by omega)]; omega
    · rw [eax₇]; omega
    · rw [esp₇]; exact hst'
    · rw [esp₇, aK]; exact hstk.sub_right (VG.Offset.sub_base _ (by omega))
    · rw [esp₇, aD]; exact hstk.sub_right (VG.Offset.sub_base _ (by omega))
    · rw [esp₇, aW]; exact hstk.sub_right (Region.sub_prefix (by omega))
  refine WP.seq (WP.mono (cryptCall_ok d s₇ hpre) fun s' hc => ?_)
  have hfr := hc.mem
  rw [aD, aW, esp₇, m₇] at hfr
  have sb' : s'.gpr .edi = B := (hc.callee .edi (by decide)).trans edi₇
  have esp' : s'.gpr .esp = s.gpr .esp := (hc.callee .esp (by decide)).trans esp₇
  have wr' : s'.wr = s.wr := hc.wr.trans wr₇
  have outSlot : ∀ o, 520 + 384 ≤ o → o + 4 ≤ 4 * 236 →
      ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 512, 8⟩ : Region), ⟨B.setWidth 64, 512⟩, below (s.gpr .esp) 16],
        Region.Disjoint ⟨addr B o, 4⟩ r := fun o h₁ h₂ r hr => by
    rw [addr_eq (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    · exact VG.Offset.disjoint_base _ (by omega) (by omega)
    · exact (hstk.sub_right (VG.Offset.sub_base _ (by omega))).symm
  have keepD : s'.mem.readW (addr B (4 * dSlot)) 32 = s.mem.readW (addr B (4 * dSlot)) 32 :=
    hfr.readW (Region.contains_self _ _) (outSlot _ (by simp only [dSlot, schedSlot]; omega)
      (by simp only [dSlot, schedSlot]; omega)) (by decide)
  have keepN : s'.mem.readW (addr B (4 * nSlot)) 32 = s.mem.readW (addr B (4 * nSlot)) 32 :=
    hfr.readW (Region.contains_self _ _) (outSlot _ (by simp only [nSlot, schedSlot]; omega)
      (by simp only [nSlot, schedSlot]; omega)) (by decide)
  have inD : InRegions s.wr (addr B (4 * dSlot)) 4 := ⟨_, hw, slotIn _ (by simp only [dSlot, schedSlot]; omega)⟩
  have inN : InRegions s.wr (addr B (4 * nSlot)) 4 := ⟨_, hw, slotIn _ (by simp only [nSlot, schedSlot]; omega)⟩
  refine wp_stm (b := .edi) (B := B) (o := 4 * dSlot) sb' (wr' ▸ inD) fun s₈ u₈ => ?_
  refine wp_stm (b := .edi) (B := B) (o := 4 * nSlot) ((congrFun u₈.gpr _).trans sb')
    ((u₈.wr.trans wr') ▸ inN) fun s₉ u₉ => WP.block_nil ?_
  have m₉ : s₉.mem = s'.mem := by
    rw [u₉.mem, u₈.gpr, u₈.mem, hc.callee .esi (by decide), hc.callee .ebp (by decide), esi₇, ebp₇, ← keepD,
      writeW_readW, ← keepN, writeW_readW]
  have g₉ : ∀ r, s₉.gpr r = s'.gpr r := fun r => by rw [u₉.gpr, u₈.gpr]
  have copyOut : ∀ r ∈ [(⟨B.setWidth 64 + BitVec.ofNat 64 512, 8⟩ : Region), ⟨B.setWidth 64, 512⟩, below (s.gpr .esp) 16],
      Region.Disjoint ⟨slotA B schedSlot, 384⟩ r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact VG.Offset.disjoint _ (.inr (by simp only [schedSlot]; omega)) (by simp only [schedSlot]; omega) (by omega)
    · exact VG.Offset.disjoint_base _ (by simp only [schedSlot]; omega) (by simp only [schedSlot]; omega)
    · exact (hstk.sub_right (VG.Offset.sub_base _ (by simp only [schedSlot]; omega))).symm
  refine ⟨by rw [g₉]; exact sb', by rw [g₉]; exact esp', ⟨?_, by rw [g₉, esp']; exact hstk, hfB⟩, ?_, fun j hj => ?_,
    by rw [u₉.rd, u₈.rd, hc.rd, rd₇], by rw [u₉.wr, u₈.wr, wr']⟩
  · rw [m₉, scheduleAt_eq_of_frame _ hfr copyOut]; exact hk
  · rw [m₉]
    refine hfr.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, VG.Offset.sub_base _ (by simp only [dirCore, schedSlot]; omega)⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, schedSlot]; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ h => h⟩
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega
    subst hj0
    have eB : blkAddr (dirCore d) B 0 = B.setWidth 64 + BitVec.ofNat 64 512 := by
      simp [blkAddr, slotA, dirCore, bufSlot]
    have ho := hc.output
    rw [aD, aK, m₇] at ho
    rw [m₉, show 4 * (dirCore d).bw = 8 from rfl, eB, bytesAt_eq, ho, blockResult_eq, dirCipher_bytes,
      show B.setWidth 64 + BitVec.ofNat 64 520 = slotA B schedSlot from rfl, hk]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Direction) : (dirCore d).bw = 2 := rfl

/-- Triple DES's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Direction) : CoreSpec (dirCore d) where
  Key := Spec.TripleDes.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.TripleDes.cipher, Spec.TripleDes.invCipher]
  layout := ⟨by simp only [dirCore]; decide, .inl rfl, by simp only [dirCore, schedSlot, bufSlot]; omega,
    by simp only [dirCore]; omega⟩
  keyArgs_congr := keyArgs_congr
  ready_frame h hesp _ _ hf _ hd := ready_frame h hesp hf hd
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

end VG.Proof.TripleDes.X86.Mode
