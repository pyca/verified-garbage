module

public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedVerified
public import VerifiedGarbage.Proof.Modes.X86_64.Core
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Impl.Sm4.X86_64.Ctr
public import VerifiedGarbage.Spec.Sm4.Cbc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Proof.Sm4.X86_64.LayersLit
public import VerifiedGarbage.Proof.Sm4.X86_64.PreparedBody
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's core for the modes on x86-64

`dirCoreSpec d`: SM4's core for the direction `d`
(`Impl.Sm4.X86_64.dirCore d`) meets what the modes need of a core
(`Proof.Modes.X86_64.CoreSpec`), with the key a schedule, its cipher
`Spec.Sm4.cipher` for encryption and `Spec.Sm4.invCipher` for decryption,
and the key ready when the masks and the table of round keys in `d`'s
order are in the scratch buffer (`ReadyAt`). `modeCoreSpec` is
encryption's, for CTR.

`prepare` is ECB's key setup, inline; `crypt` calls `vg_sm4_crypt_prepared`
(`WP.call`, with its contract on x86-64 and what it leaves in `sb`,
`cryptCallX86_64`) on the core's slots, its return address stored in the 8
bytes below `rsp`, which the core's slots are apart from. It keeps `rdx` and
`r8`, which the function never writes, and the slots' address in `sb`, where
the function moves `ws`.
-/

@[expose] public section

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (sb t0 movR)
open VG.Proof.Modes.X86_64 (ScrIn coreRegion bufRegion bufAddr Layout CoreSpec stkRegion stkList coreFrame)
open VG.Proof.Sm4 (scheduleAt_congr bytesAt_eq_blockAt ofFn_toList crypt_eq specDir)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Sm4.Prepared (Holds)

/-- The schedule at `rdi`, outside the regions `rs`, and the 8 bytes below
`rsp`, where the core's call stores its return address, apart from `rs`. -/
def KeyArgs (s : State) (rs : List Region) (k : Spec.Sm4.Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = Spec.Sm4.scheduleAt s.mem p ∧ (⟨p, 128⟩ : Region) ∈ s.rd ∧
    p.toNat + 128 ≤ 2 ^ 64 ∧ (∀ r ∈ rs, Region.Disjoint ⟨p, 128⟩ r) ∧
    8 ≤ (s.gpr .rsp).toNat ∧ ∀ r ∈ rs, Region.Disjoint (stkRegion (s.gpr .rsp) 8) r

theorem dirCore_total (d : Dir) : (dirCore d).total = 400 := rfl

theorem stkList_dirCore (d : Dir) (rsp : Addr) : stkList (dirCore d) rsp = [stkRegion rsp 8] := rfl

/-- The table, ready, and the 8 bytes below `rsp` apart from the slots. -/
def Ready (d : Dir) (s : State) (B : Addr) (k : Spec.Sm4.Schedule) : Prop :=
  ReadyAt d s.mem B k ∧ 8 ≤ (s.gpr .rsp).toNat ∧ Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * 400⟩

/-- The cipher of the direction `d`. -/
def dirCipher : Dir → Spec.Sm4.Schedule → Spec.Cbc.Cipher
  | .encrypt => Spec.Sm4.cipher
  | .decrypt => Spec.Sm4.invCipher

/-- The cipher of `d` on the 16 bytes at `p`: the 32 rounds with the round
keys in `d`'s order. -/
theorem dirCipher_bytes (d : Dir) (k : Spec.Sm4.Schedule) (m : Mem) (p : Addr) :
    dirCipher d k (bytesAt m p 16) =
      (outBlock (quads .enc (dirKeys d k) 8 (ofBlock (Spec.Sm4.blockAt m p)))).toList := by
  cases d
  · rw [dirCipher, Spec.Sm4.cipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.encryptBlock, crypt_eq]; rfl
  · rw [dirCipher, Spec.Sm4.invCipher, bytesAt_eq_blockAt, ofFn_toList, Spec.Sm4.decryptBlock, crypt_eq]; rfl

/-- A word of the core's slots outside the tail buffer is outside the regions
that are disjoint from the core's slots or within the tail buffer. -/
theorem word_disjoint {dir : Dir} {B : Addr} {d : Nat} (hd : d + 8 ≤ 8 * tableEnd)
    (hout : d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) {r : Region}
    (hr : Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    Region.Disjoint ⟨B + BitVec.ofNat 64 d, 8⟩ r := by
  rcases hr with h | h
  · exact h.sub_left (VG.Offset.sub_base B (by simp only [dirCore, slots_eq]; rw [tableEnd_eq] at hd; omega))
  · refine Region.Disjoint.sub_right ?_ h
    exact VG.Offset.disjoint B (by simp only [dirCore, tailSlot_eq] at hout ⊢; omega)
      (by simp only [tableEnd_eq] at hd; omega) (by simp only [dirCore, tailSlot_eq]; omega)

theorem readyAt_frame {dir : Dir} {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {rs : List Region}
    (h : ReadyAt dir m B k) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint (coreRegion (dirCore dir) B) r ∨ Region.Sub r (bufRegion (dirCore dir) B)) :
    ReadyAt dir m' B k := by
  have hR : ∀ d, d + 8 ≤ 8 * tableEnd → (d + 8 ≤ 8 * tailSlot ∨ 8 * tailSlot + 256 ≤ d) →
      m'.readW (B + BitVec.ofNat 64 d) 64 = m.readW (B + BitVec.ofNat 64 d) 64 := fun d h1 h2 =>
    hf.readW (Region.contains_self _ _) (fun r hr => word_disjoint h1 h2 (hd r hr)) (by decide)
  refine ⟨fun kv hkv => ?_, fun e he => (h.2 e he).congr fun j hj => ?_⟩
  · have := mask_range hkv
    rw [← h.1 kv hkv]
    exact hR (8 * kv.1) (by rw [tableEnd_eq]; omega) (.inl (by rw [tailSlot_eq]; omega))
  · exact hR (8 * tableSlot + 64 * e + 8 * j) (by rw [tableEnd_eq, tableSlot_eq]; omega)
      (.inr (by rw [tailSlot_eq, tableSlot_eq]; omega))

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Spec.Sm4.Schedule} (h : KeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi, .rsp], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (_ : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : KeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hin, hfit, hdis, hst, hsdis⟩ := h
  have hsp : s'.gpr .rsp = s.gpr .rsp := hr .rsp (by simp)
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, by rw [hrd]; exact hin, hfit, hdis,
    by rw [hsp]; exact hst, by rw [hsp]; exact hsdis⟩
  rw [hk]
  exact (scheduleAt_congr fun i hi => hf.bytes (R := ⟨p, 128⟩) hdis (by show 128 ≤ 2 ^ 64; omega) hi).symm

/-- The table, through memory that differs only apart from the working space. -/
theorem holds_frame {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    {rs : List Region} (h : Holds layout m B k d) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨B, 8 * slots⟩ r) : Holds layout m' B k d :=
  fun r hr i hi => by
    have hr' := hr
    rw [layout_table] at hr'
    have hi' : r.1 + i < 8 * slots := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
    rw [hf.bytes (R := ⟨B, 8 * slots⟩) hd (by show 8 * slots ≤ 2 ^ 64; rw [slots_eq]; omega) hi']
    exact h _ hr i hi

/-- The table survives what a batch keeps. -/
theorem holds_of_keeps {m m' : Mem} {B : Addr} {k : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction}
    (h : Holds layout m B k d) (hk : Proof.Sm4.Prepared.Keeps B slots layout.cryptScratch m m') :
    Holds layout m' B k d := fun r hr i hi => by
  have hr' := hr
  rw [layout_table] at hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  have hb : r.1 + i < 8 * slots ∧ ((384 ≤ r.1 + i ∧ r.1 + i < 408) ∨ (1024 ≤ r.1 + i ∧ r.1 + i < 3072)) := by
    rw [slots_eq]; rcases hr' with rfl | rfl <;> dsimp only at hi ⊢ <;> omega
  rw [hk (r.1 + i) hb.1 (by
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    rw [evenSlot_eq, grpSlot_eq, tableSlot_eq, savedSlot_eq, slots_eq]
    omega)]
  exact h _ hr i hi

/-- A block, through memory that differs only apart from it. -/
theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 16⟩ r) : Spec.Sm4.blockAt m' p = Spec.Sm4.blockAt m p := by
  simp only [Spec.Sm4.blockAt]
  congr 1
  funext j
  exact hf.bytes (R := ⟨p, 16⟩) hd (by show 16 ≤ 2 ^ 64; omega) j.isLt

/-- Block `j` of blocks transformed by ECB. -/
theorem blockAt_of_ecb {K : Spec.Sm4.Schedule} {d : Spec.Sm4.Direction} {m m' : Mem} {D : Addr} {n : Nat}
    (h : Spec.Sm4.blocksAt m' D n = Spec.Sm4.ecb K d (Spec.Sm4.blocksAt m D n)) {j : Nat} (hj : j < n) :
    Spec.Sm4.blockAt m' (D + BitVec.ofNat 64 (16 * j)) =
      Proof.Sm4.blockFn K d (Spec.Sm4.blockAt m (D + BitVec.ofNat 64 (16 * j))) := by
  have := congrArg (fun l => l[j]?) h
  rw [Proof.Sm4.ecb_eq] at this
  simpa [Spec.Sm4.blocksAt, hj] using this

/-- Running from `s` with a region within its writable ones added to them. -/
theorem WP.widen_wr {c : Prog isa} {s : State} {r : Region} (hr : Covers [r] s.wr) {Q : State → Prop}
    (h : WP isa c (s.withRegions s.rd (r :: s.wr)) fun s' => Q (s'.withRegions s.rd s.wr)) : WP isa c s Q := by
  obtain ⟨t, s', he, hq⟩ := h
  have := Exec.widen he (Covers.append (Covers.refl _) (Covers.cons hr (Covers.refl _))) (Covers.cons hr (Covers.refl _))
  simp only [State.withRegions_rd, State.withRegions_withRegions, State.withRegions_self] at this
  exact ⟨t, _, this, hq⟩

/-- The key setup, with ECB's scratch buffer among the writable regions. -/
theorem prepare_core (d : Dir) {s : State} {B p : Addr} (hB : s.gpr sb = B) (hw : (⟨B, 8 * slots⟩ : Region) ∈ s.wr)
    (fitB : B.toNat + 8 * slots ≤ 2 ^ 64) (hp : s.gpr .rdi = p) (hin : (⟨p, 128⟩ : Region) ∈ s.rd)
    (hfit : p.toNat + 128 ≤ 2 ^ 64) (hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 8 * slots⟩) :
    WP isa (dirCore d).prepare s fun s' => ReadyAt d s'.mem B (Spec.Sm4.scheduleAt s.mem p) ∧ s'.gpr sb = B ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame [⟨B, 8 * tableEnd⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, -, g₁, rd₁, wr₁, f₁⟩ := setMasks_ok (b := B) keyMasks hB hw
    (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega) (by decide)
  have hsch : Spec.Sm4.scheduleAt s₁.mem p = Spec.Sm4.scheduleAt s.mem p :=
    scheduleAt_congr fun i hi => f₁.bytes (R := ⟨p, 128⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hsep.sub_right (Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega))) (by show 128 ≤ 2 ^ 64; omega) hi
  have b₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  have hpre : SchedPre s₁ B p := ⟨b₁, by rw [wr₁]; exact hw, fitB,
    List.mem_append_left _ (by rw [rd₁]; exact hin), hfit, hsep⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.mono (keys_wp d hpre (by rw [g₁ _ (by decide), hp]) v₁) fun s₂ k₂ => ?_
  have b₂ : s₂.gpr sb = B := k₂.pre.base
  have keep : ∀ r, r ∉ sboxWrites → r ≠ .rsi → r ≠ .rdi → r ≠ t0 → s₂.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [k₂.regs r h1 h2 h3, g₁ r h4]
  refine ⟨⟨k₂.masks.at b₂, fun e he => ?_⟩, b₂, keep _ (by decide) (by decide) (by decide) (by decide),
    keep _ (by decide) (by decide) (by decide) (by decide), keep _ (by decide) (by decide) (by decide) (by decide), ?_⟩
  · have := k₂.key.keys e he
    rw [b₂, hsch] at this
    exact this
  · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact Region.sub_prefix (by rw [tableSlot_eq]; show 8 * 128 ≤ 8 * tableEnd; rw [tableEnd_eq]; omega)⟩).trans
      k₂.frame

theorem prepare_wp (d : Dir) {s : State} {B : Addr} {rs : List Region} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hR : (⟨B, 8 * (dirCore d).total⟩ : Region) ∈ rs) (hk : KeyArgs s rs k) :
    WP isa (dirCore d).prepare s fun s' => Ready d s' B k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, rfl, hin, hfit, hdis, hst, hsdis⟩ := hk
  have hfB := hs.fit
  rw [dirCore_total] at hfB
  have hsub : Covers [⟨B, 8 * slots⟩] s.wr := Covers.of_sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, hs.wr, 0, by simp, by show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega⟩
  have hsep : Region.Disjoint ⟨p, 128⟩ ⟨B, 8 * slots⟩ :=
    (hdis _ hR).sub_right (Region.sub_prefix (by rw [dirCore_total, slots_eq]; omega))
  refine WP.widen_wr hsub (WP.mono (prepare_core d (s := s.withRegions s.rd (⟨B, 8 * slots⟩ :: s.wr)) hB
    List.mem_cons_self (by rw [slots_eq]; omega) hp hin hfit hsep) fun s' ⟨hr', b', rsp', rdx', r8', f'⟩ => ?_)
  change ReadyAt d s'.mem B (Spec.Sm4.scheduleAt s.mem p) at hr'
  change s'.gpr .rsp = s.gpr .rsp at rsp'
  change Frame [⟨B, 8 * tableEnd⟩] s.mem s'.mem at f'
  change Ready d s' B _ ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rdx = s.gpr .rdx ∧
    s'.gpr .r8 = s.gpr .r8 ∧ Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧ s.rd = s.rd ∧ s.wr = s.wr
  refine ⟨⟨hr', by rw [rsp']; exact hst, by rw [rsp', ← dirCore_total d]; exact hsdis _ hR⟩, b', rsp', rdx', r8',
    f'.sub fun r hr => ?_, rfl, rfl⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore, tableEnd_eq, slots_eq]; omega)⟩

/-- A register `vg_sm4_crypt_prepared` never writes. -/
theorem crypt_keeps {r : Reg} (h : cryptPrepared.allInstrs (fun i => !Taint.clobbers i r) = true) :
    ∀ i ∈ instrs cryptPrepared, Taint.clobbers i r = false := by
  rw [Code.allInstrs_eq, List.all_eq_true] at h
  exact fun i hi => by simpa using h i hi

theorem crypt_nosp : NoSp cryptPrepared := crypt_keeps (by lit_decide)

theorem crypt_depth : Code.depth cryptPrepared = 0 := rfl

theorem crypt_wp (d : Dir) {s : State} {B : Addr} {k : Spec.Sm4.Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore d).total) (hr : Ready d s B k) :
    WP isa (dirCore d).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .r8 = s.gpr .r8 ∧ Ready d s' B k ∧
      Frame (coreFrame (dirCore d) B (s.gpr .rsp)) s.mem s'.mem ∧
      (∀ j < (dirCore d).G, bytesAt s'.mem (bufAddr (dirCore d) B j) 16 =
        dirCipher d k (bytesAt s.mem (bufAddr (dirCore d) B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨hready, hst, sW⟩ := hr
  have hw := hs.wr
  have hfit := hs.fit
  simp only [dirCore_total] at hw hfit
  have hH : Holds layout s.mem B k (specDir d) := by
    refine holds_of_words ?_
    rw [ofSpecDir_specDir]
    exact words_of_readyAt hready
  show WP isa cryptCall s _
  refine WP.seq ?_
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s .rdi sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movImm_ok s₂ .rsi (BitVec.ofNat 64 slots)
  refine WP.of_runBlock ⟨s₃, by
    rw [show ([movR .rdi sb, .movImm64 .rsi (BitVec.ofNat 64 slots)] : List Instr) =
      [movR .rdi sb] ++ [.movImm64 .rsi (BitVec.ofNat 64 slots)] from rfl, runBlock_app, e₂, Option.bind_some, e₃], ?_⟩
  have m₃' : s₃.mem = s.mem := by rw [m₃, m₂]
  have rd₃' : s₃.rd = s.rd := by rw [rd₃, rd₂]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂]
  have rsp₃ : s₃.gpr .rsp = s.gpr .rsp := by rw [o₃ _ (by decide), o₂ _ (by decide)]
  have rdi₃ : s₃.gpr .rdi = B := by rw [o₃ _ (by decide), r₂, hB]
  have rsi₃ : s₃.gpr .rsi = BitVec.ofNat 64 slots := r₃
  have rdx₃ : s₃.gpr .rdx = s.gpr .rdx := by rw [o₃ _ (by decide), o₂ _ (by decide)]
  have r8₃ : s₃.gpr .r8 = s.gpr .r8 := by rw [o₃ _ (by decide), o₂ _ (by decide)]
  have hE := (s.gpr .rsp).isLt
  have stS : Region.Disjoint (stkRegion (s.gpr .rsp) 8) ⟨B, 8 * slots⟩ :=
    sW.sub_right (Region.sub_prefix (by rw [slots_eq]; omega))
  -- The return address the call stores.
  have hret : Frame [stkRegion (s.gpr .rsp) 8] s₃.mem s₃.callEntry.mem := by
    rw [State.callEntry_mem, rsp₃]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega))
  have hHE : Holds layout s₃.callEntry.mem B k (specDir d) :=
    holds_frame (m := s₃.mem) (by rw [m₃']; exact hH) hret fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact stS.symm
  let sE := s₃.callEntry.withRegions [] [⟨B, 8 * slots⟩]
  have eRdi : sE.gpr .rdi = B := by
    show s₃.callEntry.gpr .rdi = B; rw [State.callEntry_gpr _ (by decide), rdi₃]
  have eRsi : sE.gpr .rsi = BitVec.ofNat 64 slots := by
    show s₃.callEntry.gpr .rsi = _; rw [State.callEntry_gpr _ (by decide), rsi₃]
  have eRsp : sE.gpr .rsp = s.gpr .rsp - 8 := by
    show s₃.callEntry.gpr .rsp = _; rw [State.callEntry_rsp, rsp₃]
  have tsl : (BitVec.ofNat 64 slots).toNat = slots := by rw [slots_eq]; rfl
  have hsub : ∀ r ∈ ([⟨B, 8 * slots⟩] : List Region), ∃ r' ∈ s₃.wr, ∃ off,
      r.base = r'.base + BitVec.ofNat 64 off ∧ off + r.len ≤ r'.len := fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, by rw [wr₃']; exact hs.wr, 0, by simp, by
      show 0 + 8 * slots ≤ 8 * (dirCore d).total; rw [dirCore_total, slots_eq]; omega⟩
  refine WP.call (c := cryptPrepared) (k := cryptCallX86_64) cryptCall_correct crypt_nosp (by rw [crypt_depth]; decide)
    (rd := []) (wr := [⟨B, 8 * slots⟩]) ?_ ?_ ?_ ?_
  · change cryptX86_64.pre sE
    simp only [cryptX86_64]
    rw [eRdi, eRsi, eRsp, tsl]
    refine ⟨rfl, by rw [Nat.mul_comm]; rfl, ?_, by rw [slots_eq]; omega, by rw [size_eq], k, specDir d, hHE⟩
    rw [Nat.mul_comm slots 8]
    exact stS
  · exact Covers.right (Covers.of_sub hsub)
  · exact Covers.of_sub hsub
  intro s' rd' wr' cs frame clob ⟨s₂', mem₂, g₂', post, hsb⟩
  change cryptX86_64.post sE s₂' at post
  simp only [cryptX86_64] at post
  rw [eRdi, eRsi, tsl, mem₂] at post
  obtain ⟨hE', hK⟩ := post
  have hEcb := hE' k (specDir d) hHE
  rw [crypt_depth, rsp₃, m₃'] at frame
  have frame' : Frame [⟨B, 8 * slots⟩, stkRegion (s.gpr .rsp) 8] s.mem s'.mem := frame
  have sb' : s'.gpr sb = B := by rw [← g₂' _ (by decide)]; exact hsb.trans eRdi
  have rsp' : s'.gpr .rsp = s.gpr .rsp := (cs .rsp (by decide)).trans rsp₃
  have rdx' : s'.gpr .rdx = s.gpr .rdx := (clob .rdx (crypt_keeps (by lit_decide))).trans rdx₃
  have r8' : s'.gpr .r8 = s.gpr .r8 := (clob .r8 (crypt_keeps (by lit_decide))).trans r8₃
  refine ⟨sb', rsp', rdx', r8', ⟨?_, by rw [rsp']; exact hst, by rw [rsp']; exact sW⟩, ?_, fun j hj => ?_,
    by rw [rd', rd₃'], by rw [wr', wr₃']⟩
  · have := readyAt_of_words (words_of_holds (holds_of_keeps hHE hK))
    rw [ofSpecDir_specDir] at this
    exact this
  · refine frame'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by simp only [dirCore]; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (by rw [stkList_dirCore]; exact List.mem_singleton_self _), fun _ h => h⟩
  · have hj' : j < 16 := hj
    have ha : bufAddr (dirCore d) B j = B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j) := by
      simp only [bufAddr, dirCore, layout, VG.Offset.add_add]
    have hblk : Spec.Sm4.blockAt sE.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) =
        Spec.Sm4.blockAt s.mem (B + BitVec.ofNat 64 layout.buf + BitVec.ofNat 64 (16 * j)) := by
      rw [← m₃']
      refine blockAt_frame hret fun r hr => ?_
      rw [List.mem_singleton] at hr; subst hr
      rw [VG.Offset.add_add]
      exact (stS.sub_right (VG.Offset.sub_base _ (by simp only [layout, tailSlot_eq, slots_eq]; omega))).symm
    rw [ha, dirCipher_bytes, bytesAt_eq_blockAt, blockAt_of_ecb hEcb hj', hblk, quads_spec]

/-- The core's blocks are two words. -/
@[simp] theorem dirCore_bw (d : Dir) : (dirCore d).bw = 2 := rfl

/-- SM4's core for the direction `d` meets what the modes need. -/
def dirCoreSpec (d : Dir) : CoreSpec (dirCore d) where
  Key := Spec.Sm4.Schedule
  cipher := dirCipher d
  KeyArgs := KeyArgs
  Ready := Ready d
  cipher_len _ _ := by cases d <;> simp [dirCipher, Spec.Sm4.cipher, Spec.Sm4.invCipher]
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ hg := by
    have hsp : _ := hg .rsp (by simp only [Modes.X86_64.modeRegs, dirCore]; decide)
    exact ⟨readyAt_frame h.1 hf hd, by rw [hsp]; exact h.2.1, by rw [hsp]; exact h.2.2⟩
  prepare_wp := prepare_wp d
  crypt_wp := crypt_wp d

/-- SM4's core for encryption, for CTR. -/
abbrev modeCoreSpec : CoreSpec modeCore := dirCoreSpec .encrypt

end VG.Proof.Sm4.X86_64
