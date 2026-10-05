import VerifiedGarbage.Spec.Siv.Contract
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-SIV with its working space as an argument

`vg_aes_siv_init`, `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` keep their
working space in a frame of their own (`Verified.stackScratch`,
`Verified.stackArgScratchL`, `Arm.Verified.stackScratchL`, …), around code
proved with the working space as a last argument: `initScratchContract`,
`encryptScratchContract` and `decryptScratchContract` are the shared
contracts with a `scratch` buffer of 2560 bytes, or a `work` buffer of 2576,
appended, whatever it holds.

Where the frame holds a copy of the arguments passed on the stack, the pre-
and postconditions, and `decrypt`'s leak, must read the memory on entry only
within the function's buffers and its list of slices: for `init` the key
(`initPost_local`); for `encrypt` and `decrypt` (`encryptPost_local`,
`decryptPost_local`, `decryptLeak_local`) the data, the synthetic IV, the
components of associated data and their descriptors (`components_congr`)
and, for `rounds` of 10, 12 or 14, the round keys and subkeys in the key
context's 512 bytes (`ctxMac_congr`, `ctxCiph_congr`). The contracts take the
lengths and the number of components cut to the width of a pointer, at most
the ones the buffers and the list are made of, so this holds for any width
(`components_congr_le`).
-/

namespace VG.Proof.AesSiv

open VG.Spec.Siv

/-- `vg_aes_siv_init` with `scratch: *mut [u64; 320]`. -/
def initScratchSig : Sig where
  params := [("key", .slice false .u8 "key_len"), ("ctx", .array true .u64 64),
    ("scratch", .array true .u64 320)]

/-- `initContract`, whatever `scratch` is. -/
def initScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  initScratchSig.contract A
    (pre := fun key keyLen ctx _scratch => initPre A.ptrBits key keyLen ctx)
    (post := fun key keyLen ctx _scratch => initPost A.ptrBits key keyLen ctx)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_siv_encrypt` with `work: *mut [u64; 322]`. -/
def encryptScratchSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array true .u8 16), ("work", .array true .u64 322)]

/-- `encryptContract`, whatever `work` is. -/
def encryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  encryptScratchSig.contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      encryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      encryptPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)

/-- `vg_aes_siv_decrypt` with `work: *mut [u64; 322]`. -/
def decryptScratchSig : Sig where
  params := [("ctx", .array false .u64 64), ("rounds", .int .usize true),
    ("ads", .slices .u8 "ads_count"), ("data", .slice true .u8 "len"),
    ("siv", .array false .u8 16), ("work", .array true .u64 322)]
  ret := some .u32

/-- `decryptContract`, whatever `work` is. -/
def decryptScratchContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  decryptScratchSig.contract A
    (pre := fun ctx rounds ads adsCount data len siv _work =>
      decryptPre A.ptrBits ctx rounds ads adsCount data len siv)
    (post := fun ctx rounds ads adsCount data len siv _work =>
      decryptPost A.ptrBits ctx rounds ads adsCount data len siv)
    (writeArgs := true) (stack := stack)
    (leak := some fun ctx rounds ads adsCount data len siv _work =>
      decryptLeak A.ptrBits ctx rounds ads adsCount data len siv)

/-! ## Locality -/

theorem bytesAt_congr {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- The bytes of a region on which two memories agree. -/
theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) :=
  fun _ hi => (h _ (Region.contains_ofNat p hi)).symm

/-- `bytesAt_congr`, at an offset `d` into the agreeing bytes. -/
private theorem bytesAt_congr_off {m₁ m₂ : Mem} {p : Addr} {d n N : Nat} (hn : d + n ≤ N)
    (h : ∀ i < N, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n :=
  bytesAt_congr fun i hi => by rw [Offset.add_add]; exact h _ (by omega)

/-- The PRF of a key context, for at most 14 rounds, is in its 512 bytes. -/
theorem ctxMac_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 14)
    (h : ∀ i < 512, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxMac m₂ p nr = ctxMac m₁ p nr := by
  simp only [ctxMac, schedCiph]
  rw [bytesAt_congr fun i hi => h i (by omega),
    show p + 240 = p + BitVec.ofNat 64 240 from rfl, show p + 256 = p + BitVec.ofNat 64 256 from rfl,
    bytesAt_congr_off (by omega) h, bytesAt_congr_off (by omega) h]

/-- The cipher of a key context, for at most 14 rounds, is in its 512 bytes. -/
theorem ctxCiph_congr {m₁ m₂ : Mem} {p : Addr} {nr : Nat} (hn : nr ≤ 14)
    (h : ∀ i < 512, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    ctxCiph m₂ p nr = ctxCiph m₁ p nr := by
  simp only [ctxCiph, schedCiph]
  rw [show p + 272 = p + BitVec.ofNat 64 272 from rfl, bytesAt_congr_off (by omega) h]

/-- The components of associated data are in the descriptors and the slices
they list. -/
theorem components_congr {pb : Nat} {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ r ∈ Sig.descRegion pb p n :: Sig.listed pb m₁ .u8 p n, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    components pb m₂ p n = components pb m₁ p n := by
  simp only [components]
  rw [Sig.listed_congr pb .u8 p n (h _ List.mem_cons_self)]
  refine List.map_congr_left fun r hr => ?_
  rw [← Sig.listed_congr pb .u8 p n (h _ List.mem_cons_self)] at hr
  exact bytesAt_congr (agree_of (h r (List.mem_cons_of_mem _ hr)))

/-- `components_congr`, for the first `N'` of `N` descriptors. -/
theorem components_congr_le {pb : Nat} {m₁ m₂ : Mem} {p : Addr} {N' N : Nat} (hle : N' ≤ N)
    (h : ∀ r ∈ Sig.descRegion pb p N :: Sig.listed pb m₁ .u8 p N, ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    components pb m₂ p N' = components pb m₁ p N' := by
  refine components_congr fun r hr a ha => ?_
  rcases List.mem_cons.mp hr with rfl | hr
  · refine h _ List.mem_cons_self a ?_
    simp only [Sig.descRegion, Region.Contains] at ha ⊢
    exact Nat.le_trans ha (Nat.mul_le_mul_right _ hle)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact h _ (List.mem_cons_of_mem _ (List.mem_map.mpr
      ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) hle), rfl⟩)) a ha

theorem le14 {n : Nat} (h : n = 10 ∨ n = 12 ∨ n = 14) : n ≤ 14 := by omega

/-- The inputs of `encryptWith` and `decryptWith` on the memory `m₂` are those
on `m₁` where they agree on the buffers and the list of slices: the lengths
the contracts take, cut to `pb` bits, are at most the buffers' and the
list's. -/
private theorem inputs_local {pb : Nat} {m₁ m₂ : Mem} {ctx ads data siv : Addr} {rd cnt len : BitVec 64}
    (hn : (rd.setWidth pb).toNat ≤ 14)
    (hc : ∀ i < 64 * 8, m₂ (ctx + BitVec.ofNat 64 i) = m₁ (ctx + BitVec.ofNat 64 i))
    (hD : ∀ i < len.toNat, m₂ (data + BitVec.ofNat 64 i) = m₁ (data + BitVec.ofNat 64 i))
    (hV : ∀ i < 16 * 1, m₂ (siv + BitVec.ofNat 64 i) = m₁ (siv + BitVec.ofNat 64 i))
    (hL : ∀ r ∈ Sig.descRegion pb ads cnt.toNat :: Sig.listed pb m₁ .u8 ads cnt.toNat,
      ∀ a, r.Contains a 1 → m₁ a = m₂ a) :
    ctxMac m₂ ctx (rd.setWidth pb).toNat = ctxMac m₁ ctx (rd.setWidth pb).toNat ∧
      ctxCiph m₂ ctx (rd.setWidth pb).toNat = ctxCiph m₁ ctx (rd.setWidth pb).toNat ∧
      components pb m₂ ads (cnt.setWidth pb).toNat = components pb m₁ ads (cnt.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ data (len.setWidth pb).toNat = Spec.Aes.bytesAt m₁ data (len.setWidth pb).toNat ∧
      Spec.Aes.bytesAt m₂ siv 16 = Spec.Aes.bytesAt m₁ siv 16 := by
  have := Nat.mod_le cnt.toNat (2 ^ pb)
  have := Nat.mod_le len.toNat (2 ^ pb)
  simp only [BitVec.toNat_setWidth] at hn ⊢
  exact ⟨ctxMac_congr hn fun i hi => hc i (by omega), ctxCiph_congr hn fun i hi => hc i (by omega),
    components_congr_le (by omega) hL, bytesAt_congr fun i hi => hD i (by omega),
    bytesAt_congr fun i hi => hV i (by omega)⟩

variable (pb : Nat)

theorem initPre_local : ∀ vs m₁ m₂, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPre pb) vs m₁ → Curry.apply (initSig.words pb) (initPre pb) vs m₂
  | [_, _, _], _, _, _, _, h => h

theorem initPost_local : ∀ vs m₁ m₂ m' r, vs.length = (initSig.words pb).length →
    (∀ b ∈ Sig.bufs initSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (initSig.words pb) (initPost pb) vs m₁ m' r →
      Curry.apply (initSig.words pb) (initPost pb) vs m₂ m' r
  | [key, kl, _], m₁, m₂, m', r, _, hb, h => by
    simp only [initSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hk := agree_of hb.1
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr] (initPost pb) _ m₂ m' r
    dsimp only [Curry.apply, initPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le kl.toNat (2 ^ pb)
    rw [bytesAt_congr (n := (kl.setWidth pb).toNat) fun i hi => hk i (by
      rw [BitVec.toNat_setWidth] at hi; omega)]
    exact h

theorem encryptPre_local : ∀ vs m₁ m₂, vs.length = (encryptSig.words pb).length →
    (∀ b ∈ Sig.bufs encryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ encryptSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (encryptSig.words pb) (encryptPre pb) vs m₁ →
      Curry.apply (encryptSig.words pb) (encryptPre pb) vs m₂
  | [_, _, _, _, _, _, _], _, _, _, _, _, h => h

theorem decryptPre_local : ∀ vs m₁ m₂, vs.length = (decryptSig.words pb).length →
    (∀ b ∈ Sig.bufs decryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ decryptSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (decryptSig.words pb) (decryptPre pb) vs m₁ →
      Curry.apply (decryptSig.words pb) (decryptPre pb) vs m₂
  | [_, _, _, _, _, _, _], _, _, _, _, _, h => h

/-- `encryptPost` reads the memory on entry only within the buffers and the list
of slices -/
theorem encryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (encryptSig.words pb).length →
    (∀ b ∈ Sig.bufs encryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ encryptSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (encryptSig.words pb) (encryptPost pb) vs m₁ m' r →
      Curry.apply (encryptSig.words pb) (encryptPost pb) vs m₂ m' r
  | [ctx, rd, ads, cnt, data, len, siv], m₁, m₂, m', r, _, hb, hl, h => by
    simp only [encryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [encryptSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (encryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (encryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, encryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, e₂, e₃, e₄, -⟩ := inputs_local (pb := pb) (siv := siv) (le14 hr) (agree_of hb.1) (agree_of hb.2.1)
      (agree_of hb.2.2) hl
    rw [e₁, e₂, e₃, e₄]
    exact h hr

/-- `decryptPost` reads the memory on entry only within the buffers and the list
of slices -/
theorem decryptPost_local : ∀ vs m₁ m₂ m' r, vs.length = (decryptSig.words pb).length →
    (∀ b ∈ Sig.bufs decryptSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    (∀ r ∈ Sig.lists pb m₁ decryptSig.params vs, ∀ a, r.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (decryptSig.words pb) (decryptPost pb) vs m₁ m' r →
      Curry.apply (decryptSig.words pb) (decryptPost pb) vs m₂ m' r
  | [ctx, rd, ads, cnt, data, len, siv], m₁, m₂, m', r, _, hb, hl, h => by
    simp only [decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [decryptSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (decryptPost pb) _ m₁ m' r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (decryptPost pb) _ m₂ m' r
    dsimp only [Curry.apply, decryptPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
    intro hr
    obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := inputs_local (pb := pb) (le14 hr) (agree_of hb.1) (agree_of hb.2.1)
      (agree_of hb.2.2) hl
    rw [e₁, e₂, e₃, e₄, e₅]
    exact h hr

/-- `decryptLeak` reads the memory only within the buffers and the list of
slices -/
theorem decryptLeak_local : Sig.LeakLocalL pb decryptSig (some (decryptLeak pb))
  | [ctx, rd, ads, cnt, data, len, siv], m₁, m₂, _, hb, hl => by
    simp only [decryptSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
    simp only [decryptSig, Sig.lists, List.append_nil] at hl
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
      ArgWord.int pb, ArgWord.addr] (decryptLeak pb) _ m₁ =
      Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.int pb, ArgWord.addr,
        ArgWord.int pb, ArgWord.addr] (decryptLeak pb) _ m₂
    dsimp only [Curry.apply, decryptLeak, ArgWord.ofRaw, IntTy.bits]
    by_cases hr : (rd.setWidth pb).toNat = 10 ∨ (rd.setWidth pb).toNat = 12 ∨ (rd.setWidth pb).toNat = 14
    · simp only [hr, not_true_eq_false, ↓reduceIte]
      obtain ⟨e₁, e₂, e₃, e₄, e₅⟩ := inputs_local (pb := pb) (le14 hr) (agree_of hb.1) (agree_of hb.2.1)
        (agree_of hb.2.2) hl
      simp only [e₁, e₂, e₃, e₄, e₅]; congr
    · simp only [hr, not_false_eq_true, ↓reduceIte]

end VG.Proof.AesSiv
