module

public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Front
public import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
public import VerifiedGarbage.Proof.AesOcb.X86_64.Open
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Dec
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee

/-!
# One-pass AES-OCB with AES-NI on x86-64: `front`

Untrusted: everything here is checked by Lean. `front enc d` is `entry`,
`Ktop` (`ktop`), `L_1`, `L_2`, `L_3` and the table `C` (`lmore`, `ctab`),
`HASH` (`hash`), `Offset_0` (`nonce`), for `open` the round keys through
`aesimc`, the data (`body`) and the tag at `W + d` (`tag`). After `entry`,
everything it writes is in `postW`, which misses the slots `entry` fills:
`L_$` and `L_0`, our caller's registers, the arguments and the address of
the tag.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith ctxCiph ctxInv ctxLstar lAt)
open VG.Proof.AesOcb.X86_64 (rv LayN PermN EnvN BufN DBufN ArgsN EntryPostN Saved entry_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys DKeys ImcInv imcKeys_okR dKeys_of_imc ofInt_natCast)
open VG.Impl.AesOcb.X86_64 (at_ ld st tmpO rndO aadO alenO sumO t2O ldO l0O dataO lenO tagO tgO tlO entry)
open VG.Impl.AesOcb.X86_64AesNi (ktop lmore ctab keys hash nonce imcPtr imcO body tag front l1O l2O l3O cO ofO ljO)
open VG.Impl.AesOcb.X86_64 (ofsO o0O botO nO nlO)
open VG.Proof.Ocb (offAt ckAt dckAt encBlocks decBlocks)
open VG.Spec.Ocb (aesInvWith)

/-- What `front` writes after `entry`, in `W`. -/
abbrev postW (W : Addr) (wn : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 0, 32⟩, ⟨W + BitVec.ofNat 64 48, 16⟩, ⟨W + BitVec.ofNat 64 96, 64⟩,
    ⟨W + BitVec.ofNat 64 256, 8⟩, ⟨W + BitVec.ofNat 64 272, 16⟩, ⟨W + BitVec.ofNat 64 320, 32⟩,
    ⟨W + BitVec.ofNat 64 384, wn - 384⟩]

theorem postW_sub {W : Addr} {wn : Nat} (hwn : 640 ≤ wn) : ∀ r ∈ postW W wn, Region.Sub r ⟨W, wn⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact LayN.wSub (by omega_arith)

/-- The slots of `W` outside `postW`. -/
theorem postW_disj {W : Addr} {wn d k : Nat} (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64)
    (hd : (64 ≤ d ∧ d + k ≤ 96) ∨ (160 ≤ d ∧ d + k ≤ 256) ∨ (288 ≤ d ∧ d + k ≤ 320)) :
    ∀ r ∈ postW W wn, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)

/-- A region of `W` within one of `postW`. -/
theorem in_postW {W : Addr} {wn d n e k : Nat} (he : (⟨W + BitVec.ofNat 64 e, k⟩ : Region) ∈ postW W wn)
    (h₁ : e ≤ d) (h₂ : d + n ≤ e + k) : ∃ r' ∈ postW W wn, Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r' :=
  ⟨_, he, Offset.sub W h₁ h₂⟩

/-- The round keys through `aesimc` at `W + imcO`. -/
theorem imcAt_of_dKeys {nr : Nat} {w : List Byte} {s : State} {W : Addr} (h : DKeys nr w s)
    (h8 : s.gpr .r8 = at' W imcO) : ImcAt nr w W s.mem := fun j h1 h2 => by
  have := (h.imc j h1 h2).2
  rw [h8, ofInt_natCast] at this
  rw [← at'_add]; exact this

/-- Bytes outside `W` are kept by a frame within `W`. -/
theorem keepOut {W : Addr} {wn : Nat} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, Region.Sub r ⟨W, wn⟩) {p : Addr} {k : Nat} (hd : (⟨p, k⟩ : Region).Disjoint ⟨W, wn⟩)
    (hk : k ≤ 2 ^ 64) : bytesAt m' p k = bytesAt m p k :=
  Proof.AesCcm.X86_64.bytesAt_frame hf (fun r hr => hd.sub_right (hs r hr)) hk

theorem entryR_sub {W : Addr} {wn : Nat} (hwn : 640 ≤ wn) :
    ∀ r ∈ [Proof.AesOcb.X86_64.entryR W], Region.Sub r ⟨W, wn⟩ := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact LayN.wSub (by omega_arith)

/-- What the pieces before the data leave. -/
structure MidPost (enc : Bool) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (wn : Nat) (s s' : State) :
    Prop where
  body : BodyPre enc s' K W SP D wn R n (ctxLstar s.mem K)
    (Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl))
  frame : Frame (Proof.AesOcb.X86_64.entryR W :: postW W wn) s.mem s'.mem
  slots : Proof.AesOcb.X86_64.Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  ld : blockAtMem s'.mem (W + BitVec.ofNat 64 ldO) = Spec.Ocb.lDollar (ctxLstar s.mem K)
  sum : blockAtMem s'.mem (W + BitVec.ofNat 64 sumO) =
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)
  key : bytesAt s'.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `mid`, after `entry` and `ktop`. -/
theorem mid_ok (enc : Bool) {s s₀ s₁ : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr} {wn : Nat}
    (Ar : ArgsN s K W SP N A D R nl al n tl T wn) (hwn : 640 ≤ wn) (hwlt : wn < 2 ^ 64)
    (hwo : enc = false → imcO + 224 ≤ wn) (hdi : s.gpr .rdi = K)
    (P₀ : EntryPostN K W SP wn R N A D nl al n tl T s s₀)
    (K₁ : KtopPost K W R tl (bytesAt s₀.mem N nl) s₀ s₁) :
    WP isa (Impl.AesOcb.X86_64AesNi.mid enc) s₁ (MidPost enc K W SP N A D R nl al n tl T wn s) := by
  have L : LayN K W SP wn := Ar.lay
  have hR := Ar.rounds
  have hw := hwlt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have rdi₀ : s₀.gpr .rdi = K := P₀.rdi.trans hdi
  have kK : (⟨K, 16 * (R + 1)⟩ : Region).Disjoint ⟨W, wn⟩ := L.k_w.sub_left (Region.sub_prefix (by omega_arith))
  have kL : (⟨K + BitVec.ofNat 64 240, 16⟩ : Region).Disjoint ⟨W, wn⟩ := L.k_w.sub_left (Offset.sub_base K (by decide))
  have key₀ : bytesAt s₀.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1)) :=
    keepOut P₀.frame (entryR_sub hwn) kK (by omega_arith)
  have N₀ : bytesAt s₀.mem N nl = bytesAt s.mem N nl :=
    keepOut P₀.frame (entryR_sub hwn) Ar.nonce.w (by have := Ar.nonce.lt; omega_arith)
  unfold Impl.AesOcb.X86_64AesNi.mid
  have E₁ : EnvN K W SP wn s₁ := P₀.env.keep (fun r hr => K₁.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) K₁.rd K₁.wr
  have F₁ : Frame (postW W wn) s₀.mem s₁.mem := K₁.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_postW (e := 96) (k := 64) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 256) (k := 8) (by simp [postW]) (by decide) (by decide)
  have rdi₁ : s₁.gpr .rdi = K := by rw [K₁.gpr _ (by decide), rdi₀]
  -- `L_1`, `L_2`, `L_3`, the table and the round keys' registers.
  simp only [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have l0₁ : blockAtMem s₁.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0 := by
    rw [Proof.Ocb.blockAtMem_frame F₁ (postW_disj hwn hw (by decide)), P₀.l0]
  refine WP.mono (lmore_ok s₁ E₁.r15 E₁.perm.w hwn hw l0₁) fun s₂ ⟨l0₂, l1₂, l2₂, l3₂, fr₂, g₂, rd₂, wr₂, x₂⟩ => ?_
  have F₂ : Frame (postW W wn) s₁.mem s₂.mem := fr₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact in_postW (e := 96) (k := 64) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 96) (k := 64) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 320) (k := 32) (by simp [postW]) (by decide) (by decide)
  have E₂ : EnvN K W SP wn s₂ := E₁.keep (fun r hr => g₂ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₂ wr₂
  rw [WP.block_append_iff]
  refine WP.mono (ctab_ok s₂ E₂.r15 E₂.perm.w hwn hw l0₂ l1₂ l2₂) fun s₃ ⟨C₃, fr₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  have F₃ : Frame (postW W wn) s₂.mem s₃.mem := fr₃.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact in_postW (e := 384) (k := wn - 384) (by simp [postW]) (by decide) (by simp only [cO]; omega_arith)
  have E₃ : EnvN K W SP wn s₃ := E₂.keep (fun r hr => g₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₃ wr₃
  have F₀₃ : Frame (postW W wn) s₀.mem s₃.mem := (F₁.trans F₂).trans F₃
  have rnd₃ : s₃.mem.readW (W + BitVec.ofNat 64 rndO) 64 = BitVec.ofNat 64 R := by
    rw [F₀₃.readW (r := ⟨W + BitVec.ofNat 64 rndO, 8⟩) (Region.contains_self _ _) (postW_disj hwn hw (by decide))
      (by decide)]
    exact P₀.slots.rounds
  refine WP.mono (keys_ok s₃ E₃.r15 rnd₃ (E₃.perm.wR (by simp only [rndO]; omega_arith) hw))
    fun s₄ ⟨rsi₄, r10₄, g₄, m₄, rd₄, wr₄, x₄⟩ => ?_
  have E₄ : EnvN K W SP wn s₄ := E₃.keep (fun r hr => g₄ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₄ wr₄
  have rdi₄ : s₄.gpr .rdi = K := by
    rw [g₄ _ (by decide) (by decide), g₃ _ (by decide) (by decide), g₂ _ (by decide), rdi₁]
  have F₀₄ : Frame (postW W wn) s₀.mem s₄.mem := by rw [m₄]; exact F₀₃
  have kW₄ : ∀ {d k : Nat}, ((64 ≤ d ∧ d + k ≤ 96) ∨ (160 ≤ d ∧ d + k ≤ 256) ∨ (288 ≤ d ∧ d + k ≤ 320)) →
      bytesAt s₄.mem (W + BitVec.ofNat 64 d) k = bytesAt s₀.mem (W + BitVec.ofNat 64 d) k := fun hd =>
    Proof.AesCcm.X86_64.bytesAt_frame F₀₄ (postW_disj hwn hw hd) (by omega_arith)
  have kR₄ : ∀ {d : Nat}, ((64 ≤ d ∧ d + 8 ≤ 96) ∨ (160 ≤ d ∧ d + 8 ≤ 256) ∨ (288 ≤ d ∧ d + 8 ≤ 320)) →
      s₄.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun hd =>
    F₀₄.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (postW_disj hwn hw hd) (by decide)
  have lstar₄ : blockAtMem s₄.mem (K + 240) = ctxLstar s.mem K := by
    rw [ctxLstar, blockAtMem, blockAtMem, show (K + 240 : Addr) = K + BitVec.ofNat 64 240 from rfl,
      keepOut F₀₄ (postW_sub hwn) kL (by decide), keepOut P₀.frame (entryR_sub hwn) kL (by decide)]
  have hc3 : ∀ {d : Nat}, (d + 16 ≤ cO ∨ cO + 112 ≤ d) → d + 16 ≤ wn →
      blockAtMem s₄.mem (W + BitVec.ofNat 64 d) = blockAtMem s₂.mem (W + BitVec.ofNat 64 d) := fun h1 h2 => by
    rw [m₄]; exact Proof.Ocb.blockAtMem_frame fr₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W h1 (by omega_arith) (by decide))
  -- `HASH`.
  have H₄ : HashPre s₄ K W SP A wn R al (ctxLstar s.mem K) := {
    env := E₄
    rdi := rdi₄
    rounds := hR
    rsi := rsi₄
    r10 := by rw [r10₄, g₄ _ (by decide) (by decide)]
    aad := by rw [kR₄ (by decide)]; exact P₀.slots.aad
    alen := by rw [kR₄ (by decide)]; exact P₀.alen
    rnd := by rw [kR₄ (by decide)]; exact P₀.slots.rounds
    buf := Ar.aad.of_eq (by rw [rd₄, rd₃, rd₂, K₁.rd, P₀.rd]) (by rw [wr₄, wr₃, wr₂, K₁.wr, P₀.wr])
    kw := L.k_w
    lstar := lstar₄
    C := fun t h1 h7 => by rw [m₄]; exact C₃ t h1 h7
    L2 := by rw [hc3 (by decide) (by simp only [l2O, Impl.AesOcb.X86_64.ohO]; omega_arith)]; exact l2₂
    L3 := by rw [hc3 (by decide) (by simp only [l3O]; omega_arith)]; exact l3₂
    wnLe := hwn
    wlt := hw }
  refine WP.seq (WP.mono (hash_ok H₄) fun s₅ HP => ?_)
  have F₅ : Frame (postW W wn) s₄.mem s₅.mem := HP.fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact in_postW (e := 384) (k := wn - 384) (by simp [postW]) (by decide) (by simp only [ofO]; omega_arith)
    · exact in_postW (e := 384) (k := wn - 384) (by simp [postW]) (by decide) (by simp only [c8O, cO]; omega_arith)
    · exact in_postW (e := 320) (k := 32) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 96) (k := 64) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 48) (k := 16) (by simp [postW]) (by decide) (by decide)
  have E₅ : EnvN K W SP wn s₅ := E₄.keep (fun r hr => HP.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) HP.rd HP.wr
  have F₀₅ : Frame (postW W wn) s₀.mem s₅.mem := F₀₄.trans F₅
  -- `Ktop` and `bottom`, kept since `ktop`.
  have rng : ∀ (d k : Nat), (d + k ≤ 16 ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (112 ≤ d ∧ d + k ≤ 128) ∨
      (160 ≤ d ∧ d + k ≤ 320)) → d + k ≤ 320 := fun d k hd => by omega_arith
  have dH : ∀ (d k : Nat), (d + k ≤ 16 ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (112 ≤ d ∧ d + k ≤ 128) ∨
      (160 ≤ d ∧ d + k ≤ 320)) → ∀ r ∈ hashW W, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    have := rng d k hd
    have e1 : ofO = 512 := rfl
    have e2 : c8O = 496 := rfl
    have e3 : ljO = 336 := rfl
    have e4 : t2O = 128 := rfl
    have e5 : sumO = 48 := rfl
    simp only [hashW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals
      exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
  have dC : ∀ (d k : Nat), (d + k ≤ 16 ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (112 ≤ d ∧ d + k ≤ 128) ∨
      (160 ≤ d ∧ d + k ≤ 320)) → ∀ r ∈ [(⟨W + BitVec.ofNat 64 cO, 112⟩ : Region)],
        (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    have := rng d k hd
    have e1 : cO = 384 := rfl
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint W (by omega_arith) (by omega_arith) (by decide)
  have dL : ∀ (d k : Nat), (d + k ≤ 16 ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (112 ≤ d ∧ d + k ≤ 128) ∨
      (160 ≤ d ∧ d + k ≤ 320)) → ∀ r ∈ [(⟨W + BitVec.ofNat 64 l1O, 16⟩ : Region), ⟨W + BitVec.ofNat 64 l2O, 16⟩,
        ⟨W + BitVec.ofNat 64 l3O, 16⟩], (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    have := rng d k hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have e1 : l1O = 96 := rfl
    have e2 : l2O = 144 := rfl
    have e3 : l3O = 320 := rfl
    rcases hr with rfl | rfl | rfl
    all_goals
      exact Offset.disjoint W (by omega_arith) (by omega_arith) (by decide)
  have hk5 : ∀ {d k : Nat}, (d + k ≤ 16 ∨ (32 ≤ d ∧ d + k ≤ 48) ∨ (112 ≤ d ∧ d + k ≤ 128) ∨
      (160 ≤ d ∧ d + k ≤ 320)) → bytesAt s₅.mem (W + BitVec.ofNat 64 d) k = bytesAt s₁.mem (W + BitVec.ofNat 64 d) k :=
    fun {d k} hd => by
      have := rng d k hd
      rw [Proof.AesCcm.X86_64.bytesAt_frame HP.fr (dH d k hd) (by omega_arith), m₄,
        Proof.AesCcm.X86_64.bytesAt_frame fr₃ (dC d k hd) (by omega_arith),
        Proof.AesCcm.X86_64.bytesAt_frame fr₂ (dL d k hd) (by omega_arith)]
  have ktop₅ : blockAtMem s₅.mem (W + BitVec.ofNat 64 tmpO) =
      ctxCiph s.mem K R (Proof.Ocb.nonceN tl (bytesAt s.mem N nl) &&& ~~~(63 : Block)) := by
    rw [blockAtMem, hk5 (by decide), ← blockAtMem, K₁.ktop, ctxCiph, ctxCiph, key₀, N₀]
  have bot₅ : s₅.mem.readW (W + BitVec.ofNat 64 botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN tl (bytesAt s.mem N nl)).extractLsb' 0 6).toNat := by
    have hb : (256 + 8 ≤ 16 ∨ (32 ≤ 256 ∧ 256 + 8 ≤ 48) ∨ (112 ≤ 256 ∧ 256 + 8 ≤ 128) ∨
        (160 ≤ 256 ∧ 256 + 8 ≤ 320)) := by decide
    rw [← N₀, ← K₁.bot, HP.fr.readW (Region.contains_self _ _) (dH _ _ hb) (by decide), m₄,
      fr₃.readW (Region.contains_self _ _) (dC _ _ hb) (by decide),
      fr₂.readW (Region.contains_self _ _) (dL _ _ hb) (by decide)]
  -- `Offset_0`.
  refine WP.seq (WP.mono (nonce_ok L E₅ (ctxCiph s.mem K R) ktop₅ bot₅ HP.rsi hwn hwlt) fun s₆ N₆ => ?_)
  have F₆ : Frame (postW W wn) s₅.mem s₆.mem := N₆.fr.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact in_postW (e := 0) (k := 32) (by simp [postW]) (by decide) (by decide)
    · exact in_postW (e := 272) (k := 16) (by simp [postW]) (by decide) (by decide)
  have E₆ : EnvN K W SP wn s₆ := E₅.keep (fun r hr => N₆.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) N₆.rd N₆.wr
  have F₀₆ : Frame (postW W wn) s₀.mem s₆.mem := F₀₅.trans F₆
  have rdi₆ : s₆.gpr .rdi = K := by rw [N₆.gpr _ (by decide), HP.gpr _ (by decide), rdi₄]
  -- What `HASH` and `nonce` keep of `W`.
  have k46 : ∀ d, ((64 ≤ d ∧ d + 16 ≤ 112) ∨ (144 ≤ d ∧ d + 16 ≤ 272) ∨ (288 ≤ d ∧ d + 16 ≤ 336) ∨
      (352 ≤ d ∧ d + 16 ≤ 496)) → blockAtMem s₆.mem (W + BitVec.ofNat 64 d) = blockAtMem s₄.mem (W + BitVec.ofNat 64 d) := by
    intro d hd
    have e1 : ofO = 512 := rfl
    have e2 : c8O = 496 := rfl
    have e3 : ljO = 336 := rfl
    have e4 : t2O = 128 := rfl
    have e5 : sumO = 48 := rfl
    have e6 : ofsO = 16 := rfl
    have e7 : o0O = 272 := rfl
    rw [Proof.Ocb.blockAtMem_frame (p := W + BitVec.ofNat 64 d) N₆.fr (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        all_goals
          exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)),
      Proof.Ocb.blockAtMem_frame (p := W + BitVec.ofNat 64 d) HP.fr (by
        intro r hr
        simp only [hashW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        all_goals
          exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith))]
  have sum₆ : blockAtMem s₆.mem (W + BitVec.ofNat 64 sumO) =
      Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al) := by
    rw [Proof.Ocb.blockAtMem_frame (p := W + BitVec.ofNat 64 sumO) N₆.fr (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        all_goals exact Offset.disjoint W (by decide) (by decide) (by decide))]
    rw [show W + BitVec.ofNat 64 sumO = at' W sumO from rfl, HP.sum, ctxCiph,
      keepOut F₀₄ (postW_sub hwn) kK (by omega_arith), key₀,
      keepOut F₀₄ (postW_sub hwn) Ar.aad.w (by have := Ar.aad.lt; omega_arith),
      keepOut P₀.frame (entryR_sub hwn) Ar.aad.w (by have := Ar.aad.lt; omega_arith)]
  -- The rest, after the round keys for `open`.
  have fin : ∀ s', (∀ x, x ≠ .r8 → s'.gpr x = s₆.gpr x) → (∀ x, x ≠ .xmm8 → s'.xmm x = s₆.xmm x) →
      Frame (if enc then [] else [⟨W + BitVec.ofNat 64 imcO, 224⟩]) s₆.mem s'.mem → s'.rd = s₆.rd → s'.wr = s₆.wr →
      (enc = false → ImcAt R (bytesAt s.mem K (16 * (R + 1))) W s'.mem) →
      MidPost enc K W SP N A D R nl al n tl T wn s s' := by
    intro s' hg hx hfC hrd hwr himc
    have dI : ∀ d k, d + k ≤ 624 → ∀ r ∈ (if enc then [] else [(⟨W + BitVec.ofNat 64 imcO, 224⟩ : Region)]),
        (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
      intro d k hd r hr
      cases enc
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        exact Offset.disjoint W (.inl (by simp only [imcO]; omega_arith)) (by omega_arith) (by decide)
      · simp at hr
    have hf : Frame (postW W wn) s₆.mem s'.mem := hfC.sub fun r hr => by
      cases enc
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hr; subst hr
        exact in_postW (e := 384) (k := wn - 384) (by simp [postW]) (by decide)
          (by have := hwo rfl; simp only [imcO] at this ⊢; omega_arith)
      · simp at hr
    have F' : Frame (postW W wn) s₀.mem s'.mem := F₀₆.trans hf
    have kR' : ∀ {d : Nat}, ((64 ≤ d ∧ d + 8 ≤ 96) ∨ (160 ≤ d ∧ d + 8 ≤ 256) ∨ (288 ≤ d ∧ d + 8 ≤ 320)) →
        s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₀.mem.readW (W + BitVec.ofNat 64 d) 64 := fun hd =>
      F'.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (postW_disj hwn hw hd) (by decide)
    have kB : ∀ d, d + 16 ≤ 624 → blockAtMem s'.mem (W + BitVec.ofNat 64 d) = blockAtMem s₆.mem (W + BitVec.ofNat 64 d) :=
      fun d hd => Proof.Ocb.blockAtMem_frame hfC (dI d 16 hd)
    have key' : bytesAt s'.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1)) := by
      rw [keepOut F' (postW_sub hwn) kK (by omega_arith), key₀]
    have hrd' : s'.rd = s.rd := by rw [hrd, N₆.rd, HP.rd, rd₄, rd₃, rd₂, K₁.rd, P₀.rd]
    have hwr' : s'.wr = s.wr := by rw [hwr, N₆.wr, HP.wr, wr₄, wr₃, wr₂, K₁.wr, P₀.wr]
    exact {
      body := {
        env := E₆.keep (fun r hr => hg r (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) hrd hwr
        rdi := by rw [hg _ (by decide)]; exact rdi₆
        rounds := hR
        rsi := by rw [hg _ (by decide)]; exact N₆.rsi
        r10 := by rw [hg _ (by decide), hg _ (by decide), N₆.r10, N₆.gpr .rdi (by decide)]
        data := by rw [kR' (by decide)]; exact P₀.slots.data
        len := by rw [kR' (by decide)]; exact P₀.slots.len
        buf := Ar.data.of_eq hrd' hwr'
        kw := L.k_w
        lstar := by
          rw [ctxLstar, blockAtMem, blockAtMem, show (K + 240 : Addr) = K + BitVec.ofNat 64 240 from rfl,
            keepOut F' (postW_sub hwn) kL (by decide), keepOut P₀.frame (entryR_sub hwn) kL (by decide)]
        C := fun t h1 h7 => by
          rw [kB _ (by simp only [cSlot, cO]; omega_arith), k46 _ (by simp only [cSlot, cO]; omega_arith)]
          exact H₄.C t h1 h7
        L2 := by
          rw [kB _ (by decide), k46 _ (by decide)]; exact H₄.L2
        L3 := by
          rw [kB _ (by decide), k46 _ (by decide)]; exact H₄.L3
        x12 := by rw [hx _ (by decide)]; exact N₆.x12
        x10 := by rw [hx _ (by decide)]; exact N₆.x10
        imc := fun h => by rw [key']; exact himc h
        wnLe := hwn
        wno := hwo
        wlt := hw }
      frame := (P₀.frame.mono (by simp)).trans (F'.mono fun r hr => List.mem_cons_of_mem _ hr)
      slots := {
        data := by rw [kR' (by decide)]; exact P₀.slots.data
        len := by rw [kR' (by decide)]; exact P₀.slots.len
        tl := by rw [kR' (by decide)]; exact P₀.slots.tl
        rounds := by rw [kR' (by decide)]; exact P₀.slots.rounds
        aad := by rw [kR' (by decide)]; exact P₀.slots.aad
        nonce := by rw [kR' (by decide)]; exact P₀.slots.nonce
        nlen := by rw [kR' (by decide)]; exact P₀.slots.nlen }
      tg := by rw [kR' (by decide)]; exact P₀.tg
      saved := fun p hp => by
        have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := by
          simp only [Impl.AesOcb.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [kR' (.inr (.inl ⟨hd.1, by omega_arith⟩))]; exact P₀.saved p hp
      ld := by
        rw [Proof.Ocb.blockAtMem_frame F' (postW_disj hwn hw (by decide))]; exact P₀.ld
      sum := by rw [kB _ (by decide)]; exact sum₆
      key := key'
      rd := hrd'
      wr := hwr' }
  cases enc
  · -- `open`: the round keys through `aesimc`.
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.seq (WP.mono (imcPtr_ok s₆ E₆.r15) fun s₇ ⟨r8₇, g₇, m₇, rd₇, wr₇, x₇⟩ => ?_)
    have hwo' := hwo rfl
    have rdi₇ : s₇.gpr .rdi = K := by rw [g₇ _ (by decide), rdi₆]
    have hscr : InRegions s₇.wr (s₇.gpr .r8) 224 := by
      rw [r8₇, wr₇]; exact E₆.perm.wW (d := imcO) (n := 224) hwo' hw
    have hsch : InRegions (s₇.rd ++ s₇.wr) (s₇.gpr .rdi) 240 := by
      rw [rdi₇, rd₇, wr₇]
      have := E₆.perm.kR (d := 0) (n := 240) (by decide)
      rwa [show K + BitVec.ofNat 64 0 = K from BitVec.add_zero K] at this
    have hsep : Region.Disjoint ⟨s₇.gpr .rdi, 240⟩ ⟨s₇.gpr .r8, 224⟩ := by
      rw [rdi₇, r8₇]; exact (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (LayN.wSub hwo')
    refine WP.mono (imcKeys_okR hR (by rw [g₇ _ (by decide)]; exact N₆.rsi) hscr hsch hsep) fun s₈ ⟨S, hI, hS⟩ => ?_
    have hK : Keys R (bytesAt s.mem K (16 * (R + 1))) s₇ := by
      have := keys_of_perm (E₆.perm.of_eq rd₇ wr₇) rdi₇ hR
      rwa [m₇, keepOut F₀₆ (postW_sub hwn) kK (by omega_arith), key₀] at this
    refine fin s₈ (fun x hx => by rw [hI.gpr, g₇ x hx]) (fun x hx => by rw [hI.xmm x hx, x₇])
      ?_ (by rw [hI.rd, rd₇]) (by rw [hI.wr, wr₇])
      (fun _ => imcAt_of_dKeys (dKeys_of_imc hK hscr hsep hI hS) (by rw [hI.gpr]; exact r8₇))
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← m₇]
    have := hI.lo
    rwa [r8₇] at this
  · simp only [↓reduceIte]
    exact WP.block_nil (fin s₆ (fun _ _ => rfl) (fun _ _ => rfl) (by simp; exact Frame.refl _ _) rfl rfl
      (fun h => absurd h (by decide)))

/-! ## The data and the tag -/

/-- The data `body` leaves, from the data `p` and its last `n % 16` bytes
`tail`. -/
def bOut (enc : Bool) (w : List Byte) (R n : Nat) (l o0 : Block) (p tail : List Byte) : List Byte :=
  (if enc then encBlocks (aesWith R w) o0 l p (n / 16) else decBlocks (aesInvWith R w) o0 l p (n / 16)) ++
    (if n % 16 > 0 then Spec.Ocb.xor tail (Spec.Ocb.toBytes (aesWith R w (offAt o0 l (n / 16) ^^^ l))) else [])

/-- The checksum `body` leaves. -/
def bCk (enc : Bool) (w : List Byte) (R n : Nat) (l o0 : Block) (p tail : List Byte) : Block :=
  (if enc then ckAt p (n / 16) else dckAt (aesInvWith R w) o0 l p (n / 16)) ^^^
    (if n % 16 > 0 then Spec.Ocb.pad (if enc then tail
      else Spec.Ocb.xor tail (Spec.Ocb.toBytes (aesWith R w (offAt o0 l (n / 16) ^^^ l)))) else 0)

/-- The offset `body` leaves. -/
def bOff (n : Nat) (l o0 : Block) : Block :=
  if n % 16 > 0 then offAt o0 l (n / 16) ^^^ l else offAt o0 l (n / 16)

/-- What `front` leaves: the data and the tag at `W + d`, from the arguments
at the start. -/
structure FrontPost (enc : Bool) (d : Nat) (K W SP N A D : Addr) (R nl al n tl : Nat) (T : Addr) (wn : Nat)
    (s s' : State) : Prop where
  env : EnvN K W SP wn s'
  frame : Frame (Proof.AesOcb.X86_64.entryR W :: (postW W wn ++ [⟨D, n⟩])) s.mem s'.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  slots : Proof.AesOcb.X86_64.Slots W R N A D nl n tl s'.mem
  tg : s'.mem.readW (W + BitVec.ofNat 64 tgO) 64 = T
  saved : Saved s'.mem W s.gpr
  out : bytesAt s'.mem D n = bOut enc (bytesAt s.mem K (16 * (R + 1))) R n (ctxLstar s.mem K)
    (Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)) (bytesAt s.mem D n)
    (bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
  tagv : blockAtMem s'.mem (W + BitVec.ofNat 64 d) =
    aesWith R (bytesAt s.mem K (16 * (R + 1)))
      (bCk enc (bytesAt s.mem K (16 * (R + 1))) R n (ctxLstar s.mem K)
          (Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)) (bytesAt s.mem D n)
          (bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) ^^^
        bOff n (ctxLstar s.mem K) (Spec.Ocb.offset0 (ctxCiph s.mem K R) tl (bytesAt s.mem N nl)) ^^^
        Spec.Ocb.lDollar (ctxLstar s.mem K)) ^^^
    Spec.Ocb.hash (ctxCiph s.mem K R) (ctxLstar s.mem K) (bytesAt s.mem A al)

/-- `body` and `tag`, after `mid`. -/
theorem back_ok (enc : Bool) (d : Nat) (hd' : d = 0 ∨ d = t2O) {s sm : State} {K W SP N A D : Addr}
    {R nl al n tl : Nat} {T : Addr} {wn : Nat}
    (Ar : ArgsN s K W SP N A D R nl al n tl T wn) (hwn : 640 ≤ wn) (hwlt : wn < 2 ^ 64)
    (M : MidPost enc K W SP N A D R nl al n tl T wn s sm) :
    WP isa (.seq (body enc) (tag d)) sm (FrontPost enc d K W SP N A D R nl al n tl T wn s) := by
  have L : LayN K W SP wn := Ar.lay
  have hR := Ar.rounds
  have hw := hwlt
  have hnl := Ar.data.lt
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with h | h | h <;> omega_arith
  have subM : ∀ r ∈ Proof.AesOcb.X86_64.entryR W :: postW W wn, Region.Sub r ⟨W, wn⟩ := fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact LayN.wSub (by omega_arith)
    · exact postW_sub hwn r hr
  have pD : bytesAt sm.mem D n = bytesAt s.mem D n := keepOut M.frame subM Ar.data.w (by omega_arith)
  have pT : bytesAt sm.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    keepOut M.frame subM (Ar.data.w.sub_left (Offset.sub_base D (by omega_arith))) (by omega_arith)
  refine WP.seq (WP.mono (body_ok enc M.body) fun sb B => ?_)
  have Eb : EnvN K W SP wn sb := M.body.env.keep (fun r hr => B.gpr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) B.rd B.wr
  -- What `body` keeps of `W`.
  have dB : ∀ e k, (e + k ≤ 112 ∨ (144 ≤ e ∧ e + k ≤ 336) ∨ (352 ≤ e ∧ e + k ≤ 496)) →
      ∀ r ∈ bodyW W D n, (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r := by
    intro e k he r hr
    have e1 : ofO = 512 := rfl
    have e2 : c8O = 496 := rfl
    have e3 : ljO = 336 := rfl
    have e4 : t2O = 128 := rfl
    have e5 : tmpO = 112 := rfl
    simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint W (by omega_arith) (by omega_arith) (by omega_arith)
    · exact (Ar.data.w.sub_right (LayN.wSub (by omega_arith))).symm
  have kBr : ∀ {e : Nat}, (e + 8 ≤ 112 ∨ (144 ≤ e ∧ e + 8 ≤ 336) ∨ (352 ≤ e ∧ e + 8 ≤ 496)) →
      sb.mem.readW (W + BitVec.ofNat 64 e) 64 = sm.mem.readW (W + BitVec.ofNat 64 e) 64 := fun he =>
    B.fr.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (dB _ 8 he) (by decide)
  have keyB : bytesAt sb.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1)) := by
    rw [Proof.AesCcm.X86_64.bytesAt_frame B.fr (fun r hr => by
      simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
      have kK : (⟨K, 16 * (R + 1)⟩ : Region).Disjoint ⟨W, wn⟩ := L.k_w.sub_left (Region.sub_prefix (by omega_arith))
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · exact kK.sub_right (LayN.wSub (by simp only [ofO]; omega_arith))
      · exact kK.sub_right (LayN.wSub (by simp only [c8O, cO]; omega_arith))
      · exact kK.sub_right (LayN.wSub (by simp only [ljO]; omega_arith))
      · exact kK.sub_right (LayN.wSub (by simp only [tmpO]; omega_arith))
      · exact kK.sub_right (LayN.wSub (by simp only [t2O]; omega_arith))
      · exact Ar.data.k.sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith), M.key]
  -- The tag.
  have hdd : d + 16 ≤ 640 := by rcases hd' with rfl | rfl <;> decide
  refine WP.mono (tag_ok Eb (by rw [B.gpr _ (by decide)]; exact M.body.rdi) hR
    (by rw [B.gpr _ (by decide), B.gpr _ (by decide)]; exact M.body.r10) B.x10 B.x12
    ((Proof.Ocb.blockAtMem_frame B.fr (dB ldO 16 (by decide))).trans M.ld)
    ((Proof.Ocb.blockAtMem_frame B.fr (dB sumO 16 (by decide))).trans M.sum) hdd hd' hwn hw)
    fun s' ⟨tv, fr', g', rsi', rd', wr'⟩ => ?_
  have dT : ∀ e k, (e + k ≤ 2 ^ 64) → (16 ≤ e ∧ e + k ≤ 128 ∨ 144 ≤ e) →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 d, 16⟩ : Region)], (⟨W + BitVec.ofNat 64 e, k⟩ : Region).Disjoint r := by
    intro e k h1 he r hr
    simp only [List.mem_singleton] at hr; subst hr
    rcases hd' with rfl | rfl
    · exact Offset.disjoint W (.inr (by omega_arith)) h1 (by decide)
    · exact Offset.disjoint W (by simp only [t2O]; omega_arith) h1 (by decide)
  have kS : ∀ {e : Nat}, 160 ≤ e → e + 8 ≤ 336 →
      s'.mem.readW (W + BitVec.ofNat 64 e) 64 = sm.mem.readW (W + BitVec.ofNat 64 e) 64 := fun h1 h2 => by
    rw [fr'.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (dT _ 8 (by omega_arith)
      (.inr (by omega_arith))) (by decide), kBr (.inr (.inl ⟨by omega_arith, h2⟩))]
  exact {
    env := Eb.keep (fun r hr => g' r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd' wr'
    frame := by
      refine ((M.frame.mono fun r hr => ?_).trans (B.fr.sub fun r hr => ?_)).trans (fr'.sub fun r hr => ?_)
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hr)
      · simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by simp [postW], Offset.sub W (e := 384) (k := wn - 384) (by decide)
            (by simp only [ofO]; omega_arith)⟩
        · exact ⟨_, by simp [postW], Offset.sub W (e := 384) (k := wn - 384) (by decide)
            (by simp only [c8O, cO]; omega_arith)⟩
        · exact ⟨_, by simp [postW], Offset.sub W (e := 320) (k := 32) (by decide) (by decide)⟩
        · exact ⟨_, by simp [postW], Offset.sub W (e := 96) (k := 64) (by decide) (by decide)⟩
        · exact ⟨_, by simp [postW], Offset.sub W (e := 96) (k := 64) (by decide) (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        rcases hd' with rfl | rfl
        · exact ⟨_, by simp [postW], Offset.sub W (e := 0) (k := 32) (by decide) (by decide)⟩
        · exact ⟨_, by simp [postW], Offset.sub W (e := 96) (k := 64) (by decide) (by decide)⟩
    rd := by rw [rd', B.rd, M.rd]
    wr := by rw [wr', B.wr, M.wr]
    slots := {
      data := by rw [kS (by decide) (by decide)]; exact M.slots.data
      len := by rw [kS (by decide) (by decide)]; exact M.slots.len
      tl := by rw [kS (by decide) (by decide)]; exact M.slots.tl
      rounds := by rw [kS (by decide) (by decide)]; exact M.slots.rounds
      aad := by rw [kS (by decide) (by decide)]; exact M.slots.aad
      nonce := by rw [kS (by decide) (by decide)]; exact M.slots.nonce
      nlen := by rw [kS (by decide) (by decide)]; exact M.slots.nlen }
    tg := by rw [kS (by decide) (by decide)]; exact M.tg
    saved := fun p hp => by
      have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := by
        simp only [Impl.AesOcb.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [kS hd.1 (by omega_arith)]; exact M.saved p hp
    out := by
      rw [Proof.AesCcm.X86_64.bytesAt_frame fr' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Ar.data.w.sub_right (LayN.wSub (by omega_arith))) (by omega_arith), B.out, pD, pT, M.key]
      rfl
    tagv := by
      rw [tv, keyB, pD, pT, M.key]
      rfl }

/-- `front`. -/
theorem front_ok (enc : Bool) (d : Nat) (hd' : d = 0 ∨ d = t2O) {s : State} {K W SP N A D : Addr}
    {R nl al n tl : Nat} {T : Addr} {wn : Nat}
    (Ar : ArgsN s K W SP N A D R nl al n tl T wn) (hwn : 640 ≤ wn) (hwlt : wn < 2 ^ 64)
    (hwo : enc = false → imcO + 224 ≤ wn) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa (front enc d) s (FrontPost enc d K W SP N A D R nl al n tl T wn s) := by
  have L : LayN K W SP wn := Ar.lay
  obtain ⟨s₀, run₀, P₀⟩ := entry_ok L Ar.perm hsp Ar.args Ar.argsW hD hn hT htl hW hdi hsi hdx hcx hr8 hr9 hwn hwlt
  unfold front
  refine WP.seq (WP.of_runBlock ⟨s₀, run₀, ?_⟩)
  refine WP.seq (WP.mono (ktop_ok L P₀.env Ar.rounds (P₀.rdi.trans hdi) P₀.slots.rounds P₀.slots.nonce
    P₀.slots.nlen P₀.slots.tl Ar.n1 Ar.n15 Ar.tag.lt (Ar.nonce.of_eq P₀.rd P₀.wr) hwn hwlt) fun s₁ K₁ => ?_)
  exact WP.seq (WP.mono (mid_ok enc Ar hwn hwlt hwo hdi P₀ K₁) fun sm M => back_ok enc d hd' Ar hwn hwlt M)

/-! ## `seal` -/

open VG.Proof.AesCcm.X86_64 (length_bytesAt bytesAt_frame) in
/-- The data's bytes past its whole blocks. -/
theorem drop_blocks (m : Mem) (D : Addr) (n : Nat) :
    (bytesAt m D n).drop (16 * (n / 16)) = bytesAt m (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
  rw [Proof.Ocb.bytesAt_drop _ _ (by omega_arith), show n - 16 * (n / 16) = n % 16 by omega_arith]

open VG.Proof.AesCcm.X86_64 (length_bytesAt bytesAt_frame) in
/-- `seal`, for its arguments. -/
theorem seal_wp' {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : ArgsN s K W SP N A D R nl al n tl T Impl.AesOcb.X86_64AesNi.sealWork) (hTw : Covers [⟨T, tl⟩] s.wr)
    (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa Impl.AesOcb.X86_64AesNi.seal s fun s' => gprPreserved s s' ∧
      Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl) (bytesAt s.mem A al)
        (bytesAt s.mem D n) = (bytesAt s'.mem D n, bytesAt s'.mem T tl) := by
  have L : LayN K W SP 640 := Ar.lay
  unfold Impl.AesOcb.X86_64AesNi.seal
  refine WP.seq (WP.mono (front_ok true tagO (.inl rfl) Ar (by decide) (by decide) (fun h => absurd h (by decide)) hsp
    hD hn hT htl hW hdi hsi hdx hcx hr8 hr9) fun s₅ F => ?_)
  -- The copy of the tag.
  refine WP.seq (WP.mono (Proof.AesOcb.X86_64.tagOut_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl (by rw [F.wr]; exact hTw)
    Ar.tag.w) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : EnvN K W SP 640 s₆ := F.env.keep g₆ rd₆ wr₆
  have F₆ : Frame [⟨T, tl⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have S₆ : Saved s₆.mem W s.gpr := fun p hp => by
    rw [← F.saved p hp]
    exact F₆.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have hd : p.2 + 8 ≤ 640 := by
        simp only [Impl.AesOcb.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (Ar.tag.w.sub_right (LayN.wSub hd)).symm) (by decide)
  -- `restore`.
  obtain ⟨s₇, run₇, hg₇, hm₇, hsp₇, _⟩ := Proof.AesOcb.X86_64.restore_ok E₆ S₆
  refine WP.of_runBlock ⟨s₇, run₇, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₇ (.rbx, Impl.AesOcb.X86_64.savO) (by decide)
    · exact hg₇ (.rbp, Impl.AesOcb.X86_64.savO + 8) (by decide)
    · rw [hsp₇, E₆.rsp, hsp]
    · exact hg₇ (.r12, Impl.AesOcb.X86_64.savO + 16) (by decide)
    · exact hg₇ (.r13, Impl.AesOcb.X86_64.savO + 24) (by decide)
    · exact hg₇ (.r14, Impl.AesOcb.X86_64.savO + 32) (by decide)
    · exact hg₇ (.r15, Impl.AesOcb.X86_64.savO + 40) (by decide)
  · rw [hm₇, hsp, F₆.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.retT) (by decide)]
    exact F.frame.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact Ar.retW.sub_right (LayN.wSub (by decide))
      · rcases List.mem_append.mp hr with hr | hr
        · exact Ar.retW.sub_right (postW_sub (by decide) r hr)
        · simp only [List.mem_singleton] at hr; subst hr; exact Ar.retD) (by decide)
  · -- The ciphertext and the tag.
    have hn := Ar.data.lt
    have ht := Ar.tag.lt
    have hout : Spec.Ocb.encryptWith (ctxCiph s.mem K R) (ctxLstar s.mem K) tl (bytesAt s.mem N nl)
        (bytesAt s.mem A al) (bytesAt s.mem D n) = (bytesAt s₅.mem D n, bytesAt s₅.mem W tl) := by
      have tv := F.tagv
      rw [show W + BitVec.ofNat 64 tagO = W from BitVec.add_zero W] at tv
      rw [Proof.Ocb.encryptWith_eq, F.out, Proof.AesOcb.X86_64.bytesAt_take_block _ _ Ar.t16, tv]
      simp only [length_bytesAt, drop_blocks, bOut, bCk, bOff, ↓reduceIte, ctxCiph]
      by_cases hr : 0 < n % 16
      · simp only [hr, gt_iff_lt, ↓reduceIte]
      · simp only [hr, gt_iff_lt, ↓reduceIte, List.append_nil]
        rw [show ∀ x : Block, x ^^^ 0 = x from fun x => BitVec.xor_zero]
    rw [hout, hm₇, bytesAt_frame F₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Ar.td.symm) (by omega_arith), m₆,
      Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) ht, length_bytesAt,
      List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]

/-! ## `open` -/

open VG.Proof.AesCcm.X86_64 (length_bytesAt bytesAt_frame) in
/-- `open`, for its arguments. -/
theorem open_wp' {s : State} {K W SP N A D : Addr} {R nl al n tl : Nat} {T : Addr}
    (Ar : ArgsN s K W SP N A D R nl al n tl T Impl.AesOcb.X86_64AesNi.openWork) (hsp : s.gpr .rsp = SP)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hT : s.mem.readW (SP + BitVec.ofNat 64 24) 64 = T)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    WP isa Impl.AesOcb.X86_64AesNi.open s fun s' => gprPreserved s s' ∧
      match Spec.Ocb.decryptWith (ctxCiph s.mem K R) (Spec.Ocb.ctxInv s.mem K R) (ctxLstar s.mem K) tl
          (bytesAt s.mem N nl) (bytesAt s.mem A al) (bytesAt s.mem D n) (bytesAt s.mem T tl) with
      | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem D n = pt
      | none => (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem D n = Spec.Ocb.zeros n := by
  have L : LayN K W SP 848 := Ar.lay
  have eW : Impl.AesOcb.X86_64AesNi.openWork = 848 := rfl
  unfold Impl.AesOcb.X86_64AesNi.open
  refine WP.seq (WP.mono (front_ok false t2O (.inr rfl) Ar (by decide) (by decide) (fun _ => by decide) hsp
    hD hn hT htl hW hdi hsi hdx hcx hr8 hr9) fun s₅ F => ?_)
  have F₅ : Frame (Proof.AesOcb.X86_64.entryR W :: (postW W 848 ++ [⟨D, n⟩])) s.mem s₅.mem := F.frame
  have subF : ∀ r ∈ Proof.AesOcb.X86_64.entryR W :: (postW W 848 ++ [⟨D, n⟩]),
      ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W, 848⟩ → (⟨p, k⟩ : Region).Disjoint ⟨D, n⟩ →
        (⟨p, k⟩ : Region).Disjoint r := fun r hr {p k} hW hDn => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hW.sub_right (LayN.wSub (by decide))
    · rcases List.mem_append.mp hr with hr | hr
      · exact hW.sub_right (postW_sub (by decide) r hr)
      · simp only [List.mem_singleton] at hr; subst hr; exact hDn
  -- The received tag, to `W`.
  have hTs : BufN W SP 848 s₅ T tl := Ar.tag.of_eq F.rd F.wr
  refine WP.seq (WP.mono (recv_ok F.env Ar.t1 Ar.t16 F.tg F.slots.tl hTs.rd Ar.tag.w) fun s₅' ⟨mr, gr, rdr, wrr⟩ => ?_)
  have E₅' : EnvN K W SP 848 s₅' := F.env.keep gr rdr wrr
  have Fr : Frame [⟨W, tl⟩] s₅.mem s₅'.mem := by
    rw [mr]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [length_bytesAt]; exact Region.contains_self _ _)
  have kr : ∀ {d : Nat}, 16 ≤ d → d + 8 ≤ 848 →
      s₅'.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ =>
    Fr.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint_base W (by have := Ar.t16; omega_arith) (by omega_arith)) (by decide)
  -- The comparison.
  refine WP.seq (WP.mono (cmp_ok E₅' Ar.t1 Ar.t16 (by rw [kr (by decide) (by decide)]; exact F.slots.tl))
    fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_)
  have E₆ : EnvN K W SP 848 s₆ := E₅'.keep (fun r hr => g₆ r
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)) rd₆ wr₆
  have F₆ : Frame [⟨W + BitVec.ofNat 64 tagO, 8⟩] s₅'.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have k₆ : ∀ {d : Nat}, 8 ≤ d → d + 8 ≤ 848 →
      s₆.mem.readW (W + BitVec.ofNat 64 d) 64 = s₅'.mem.readW (W + BitVec.ofNat 64 d) 64 := fun {d} h₁ h₂ => by
    rw [m₆, Proof.AesOcb.X86_64.readW_writeW_off _ (by simp only [tagO]; omega_arith) (by omega_arith) (by decide)]
  have hD₅ : DBufN K W SP 848 s₅' D n := Ar.data.of_eq (rdr.trans F.rd) (wrr.trans F.wr)
  let c : Bool := decide (bytesAt s₅'.mem W tl = bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl)
  -- The mask.
  refine WP.seq (WP.mono (mask_ok E₆ (c := c)
    (by rw [k₆ (by decide) (by decide), kr (by decide) (by decide)]; exact F.slots.data)
    (by rw [k₆ (by decide) (by decide), kr (by decide) (by decide)]; exact F.slots.len) (hD₅.of_eq rd₆ wr₆)
    (by rw [m₆, Mem.readW_writeW_self64]; simp only [c, decide_eq_true_eq])) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  have F₇ : Frame [⟨D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact WriteBytes.writeBytes_frame _ _ _ (by rw [Proof.AesOcb.X86_64.length_mask]; exact Region.contains_self _ _)
  -- The result, and `restore`.
  have ok₇ : s₇.mem.readW (W + BitVec.ofNat 64 0) 64 = if c then 1#64 else 0#64 := by
    rw [F₇.readW (r := ⟨W + BitVec.ofNat 64 0, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (LayN.wSub (by decide))).symm)
      (by decide), m₆]
    exact (Mem.readW_writeW_self64 _ _ _).trans (by simp only [c, decide_eq_true_eq])
  have r₀ : InRegions (s₇.rd ++ s₇.wr) (W + BitVec.ofNat 64 0) 8 := E₇.perm.wR (by decide)
  obtain ⟨s₈, run₈, rax₈, m₈, g₈, rd₈, wr₈⟩ : ∃ s₈, runBlock isa [ld .rax .r15 tagO] s₇ = some s₈ ∧
      s₈.gpr .rax = (if c then 1#64 else 0#64) ∧ s₈.mem = s₇.mem ∧ (∀ r, r ≠ .rax → s₈.gpr r = s₇.gpr r) ∧
      s₈.rd = s₇.rd ∧ s₈.wr = s₇.wr := by
    refine ⟨_, by orun [E₇.r15, r₀, ok₇], ?_, ?_, fun r h => ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true]
    · rfl
    · simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have E₈ : EnvN K W SP 848 s₈ := E₇.keep (fun r hr => g₈ r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    rd₈ wr₈
  have S₈ : Saved s₈.mem W s.gpr := fun p hp => by
    have hd : 160 ≤ p.2 ∧ p.2 + 8 ≤ 208 := by
      simp only [Impl.AesOcb.X86_64.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [m₈, F₇.readW (r := ⟨W + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (Ar.data.w.sub_right (LayN.wSub (by omega_arith))).symm)
      (by decide), k₆ (by omega_arith) (by omega_arith), kr (by omega_arith) (by omega_arith)]
    exact F.saved p hp
  obtain ⟨s₉, run₉, hg₉, hm₉, hsp₉, hax₉⟩ := Proof.AesOcb.X86_64.restore_ok E₈ S₈
  refine WP.of_runBlock ⟨s₉, by rw [Proof.AesCcm.X86_64.runBlock_append, run₈, Option.bind_some, run₉],
    ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg₉ (.rbx, Impl.AesOcb.X86_64.savO) (by decide)
    · exact hg₉ (.rbp, Impl.AesOcb.X86_64.savO + 8) (by decide)
    · rw [hsp₉, E₈.rsp, hsp]
    · exact hg₉ (.r12, Impl.AesOcb.X86_64.savO + 16) (by decide)
    · exact hg₉ (.r13, Impl.AesOcb.X86_64.savO + 24) (by decide)
    · exact hg₉ (.r14, Impl.AesOcb.X86_64.savO + 32) (by decide)
    · exact hg₉ (.r15, Impl.AesOcb.X86_64.savO + 40) (by decide)
  · have retW : (⟨SP, 8⟩ : Region).Disjoint ⟨W, 848⟩ := Ar.retW
    rw [hm₉, m₈, hsp,
      F₇.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Ar.retD) (by decide),
      F₆.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact retW.sub_right (LayN.wSub (by decide))) (by decide),
      Fr.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact retW.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))) (by decide)]
    exact F₅.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (fun r hr => subF r hr retW Ar.retD) (by decide)
  · -- The plaintext and the comparison.
    have hTn := Ar.tag.lt
    have hn := Ar.data.lt
    have recv : bytesAt s₅'.mem W tl = bytesAt s.mem T tl := by
      rw [mr, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [length_bytesAt]) (by omega_arith), length_bytesAt,
        List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil]
      exact bytesAt_frame F₅ (fun r hr => subF r hr Ar.tag.w Ar.td) (by omega_arith)
    have t2₅ : bytesAt s₅'.mem (W + BitVec.ofNat 64 t2O) tl = bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl :=
      bytesAt_frame Fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.base_disjoint W (e := t2O) (n := tl) (k := tl) (by have := Ar.t16; unfold t2O; omega_arith)
          (by have := Ar.t16; unfold t2O; omega_arith)).symm) (by omega_arith)
    have d₉ : bytesAt s₉.mem D n = if c then bytesAt s₅.mem D n else Spec.Ocb.zeros n := by
      have d₆ : bytesAt s₆.mem D n = bytesAt s₅.mem D n := by
        rw [bytesAt_frame F₆ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact Ar.data.w.sub_right (LayN.wSub (by decide)))
            (by omega_arith),
          bytesAt_frame Fr (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Ar.data.w.sub_right (Region.sub_prefix (by have := Ar.t16; omega_arith))) (by omega_arith)]
      rw [hm₉, m₈, m₇, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [Proof.AesOcb.X86_64.length_mask]) hn,
        Proof.AesOcb.X86_64.length_mask, List.drop_of_length_le (by rw [length_bytesAt]), List.append_nil, d₆]
    rw [hax₉, rax₈, d₉, F.out, Proof.Ocb.decryptWith_eq]
    simp only [length_bytesAt, drop_blocks, bOut, Bool.false_eq_true, ↓reduceIte, ctxCiph, Spec.Ocb.ctxInv]
    have tagv := F.tagv
    simp only [bCk, bOff, Bool.false_eq_true, ↓reduceIte, ctxCiph] at tagv
    have hc : ∀ x : Block, bytesAt s₅.mem (W + BitVec.ofNat 64 t2O) tl = (Spec.Ocb.toBytes x).take tl →
        (c = true ↔ (Spec.Ocb.toBytes x).take tl = bytesAt s.mem T tl) := fun x hx => by
      show decide (_ = _) = true ↔ _
      rw [recv, t2₅, hx, decide_eq_true_iff, eq_comm]
    rw [Proof.AesOcb.X86_64.bytesAt_take_block _ _ Ar.t16, tagv] at hc
    have hc := hc _ rfl
    by_cases hr : 0 < n % 16
    · simp only [hr, gt_iff_lt, ↓reduceIte] at hc ⊢
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩
    · simp only [hr, gt_iff_lt, ↓reduceIte, List.append_nil] at hc ⊢
      rw [show ∀ x : Block, x ^^^ 0 = x from fun x => BitVec.xor_zero] at hc
      by_cases hk : c = true
      · simp only [hc.mp hk, hk, ↓reduceIte]; exact ⟨by decide, trivial⟩
      · simp only [mt hc.mpr hk, hk, ↓reduceIte, Bool.false_eq_true]; exact ⟨by decide, trivial⟩

end VG.Proof.AesOcb.X86_64.AesNi
