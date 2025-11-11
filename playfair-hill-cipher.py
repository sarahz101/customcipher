# playfair_hill_full.py
# Combined Playfair (stage1) + 3x3 Hill (stage2) cipher implementation
# Includes encryption, decryption, known-plaintext Hill recovery,
# frequency analysis report, Playfair hill-climb breaker, and experiment runner.
#
# Usage:
#   python playfair_hill_full.py
#
# Output: prints encryption/decryption steps, attack simulation results, and experiment summary.

import random
import time
from collections import Counter
import math
import pprint

ALPHABET = "ABCDEFGHIKLMNOPQRSTUVWXYZ"  # Playfair merges I/J
MOD = 26

# ---------------- utility ----------------
def sanitize_text(text):
    return "".join([c.upper() for c in text if c.isalpha()])

def clean_playfair_plain(plain):
    """Heuristic to remove Playfair filler X's."""
    s = plain
    i = 0
    out = []
    while i < len(s):
        if i+2 < len(s) and s[i] == s[i+2] and s[i+1] == 'X':
            out.append(s[i])
            i += 2
        else:
            out.append(s[i])
            i += 1
    s2 = "".join(out)
    # strip trailing X padding (likely added)
    while s2.endswith('X'):
        s2 = s2[:-1]
    return s2

# ---------------- Playfair ----------------
def build_playfair_table(key):
    seen = set()
    table = []
    key = key.upper().replace("J","I")
    for ch in key:
        if ch.isalpha() and ch not in seen:
            seen.add(ch)
            table.append(ch)
    for ch in ALPHABET:
        if ch not in seen:
            seen.add(ch)
            table.append(ch)
    pos = {table[i]: (i//5, i%5) for i in range(25)}
    return table, pos

def playfair_preprocess(plaintext):
    text = sanitize_text(plaintext).replace("J","I")
    i = 0
    digraphs = []
    while i < len(text):
        a = text[i]
        b = text[i+1] if i+1 < len(text) else ''
        if b == '':
            digraphs.append(a+'X')
            i += 1
        elif a == b:
            digraphs.append(a+'X')
            i += 1
        else:
            digraphs.append(a+b)
            i += 2
    return digraphs

def playfair_encrypt(plaintext, key):
    table, pos = build_playfair_table(key)
    digraphs = playfair_preprocess(plaintext)
    cipher = []
    for a,b in digraphs:
        ra, ca = pos[a]
        rb, cb = pos[b]
        if ra == rb:
            cipher.append(table[ra*5 + ((ca+1)%5)] + table[rb*5 + ((cb+1)%5)])
        elif ca == cb:
            cipher.append(table[((ra+1)%5)*5 + ca] + table[((rb+1)%5)*5 + cb])
        else:
            cipher.append(table[ra*5 + cb] + table[rb*5 + ca])
    return "".join(cipher)

def playfair_decrypt(ciphertext, key):
    table, pos = build_playfair_table(key)
    pairs = [ciphertext[i:i+2] for i in range(0,len(ciphertext),2)]
    plain = []
    for a,b in pairs:
        ra, ca = pos[a]
        rb, cb = pos[b]
        if ra == rb:
            plain.append(table[ra*5 + ((ca-1)%5)] + table[rb*5 + ((cb-1)%5)])
        elif ca == cb:
            plain.append(table[((ra-1)%5)*5 + ca] + table[((rb-1)%5)*5 + cb])
        else:
            plain.append(table[ra*5 + cb] + table[rb*5 + ca])
    return "".join(plain)

# ---------------- Hill (3x3) ----------------
def egcd(a,b):
    if b==0:
        return (a,1,0)
    g,x1,y1 = egcd(b, a%b)
    return (g, y1, x1 - (a//b)*y1)

def modinv(a, m=MOD):
    a = a % m
    g,x,y = egcd(a,m)
    if g != 1:
        return None
    return x % m

def matrix_det_3(m):
    a,b,c = m[0]
    d,e,f = m[1]
    g,h,i = m[2]
    return (a*(e*i - f*h) - b*(d*i - f*g) + c*(d*h - e*g)) % MOD

def matrix_adj_3(m):
    a,b,c = m[0]
    d,e,f = m[1]
    g,h,i = m[2]
    adj = [
        [(e*i - f*h), -(b*i - c*h),  (b*f - c*e)],
        [-(d*i - f*g), (a*i - c*g), -(a*f - c*d)],
        [(d*h - e*g), -(a*h - b*g),  (a*e - b*d)]
    ]
    for r in range(3):
        for s in range(3):
            adj[r][s] = adj[r][s] % MOD
    return adj

def matrix_mul_3(A,B):
    rows = len(A)
    cols = len(B[0])
    res = [[0]*cols for _ in range(rows)]
    for i in range(rows):
        for j in range(cols):
            s=0
            for k in range(3):
                s += A[i][k]*B[k][j]
            res[i][j] = s % MOD
    return res

def matrix_inv_3(m):
    det = matrix_det_3(m)
    invdet = modinv(det)
    if invdet is None:
        return None
    adj = matrix_adj_3(m)
    inv = [[(invdet * adj[r][c]) % MOD for c in range(3)] for r in range(3)]
    return inv

def text_to_vectors(text):
    text = sanitize_text(text)
    while len(text)%3 != 0:
        text += 'X'
    vectors = []
    for i in range(0,len(text),3):
        chunk = text[i:i+3]
        vec = [[(ord(chunk[j]) - 65) % MOD] for j in range(3)]
        vectors.append(vec)
    return vectors

def vectors_to_text(vectors):
    chars = []
    for vec in vectors:
        for r in range(3):
            val = vec[r][0] % MOD
            chars.append(chr(val + 65))
    return "".join(chars)

def derive_hill_matrix_from_key(key_str):
    s = sanitize_text(key_str)
    if len(s) < 9:
        s = s + ("A"*(9-len(s)))
    s = s[:9]
    m = [[(ord(s[3*r + c]) - 65) % MOD for c in range(3)] for r in range(3)]
    attempts = 0
    while matrix_inv_3(m) is None and attempts < 26:
        m[2][2] = (m[2][2] + 1) % MOD
        attempts += 1
    if matrix_inv_3(m) is None:
        raise ValueError("Unable to derive invertible Hill matrix from key string.")
    return m

def hill_encrypt(text, key_matrix):
    vecs = text_to_vectors(text)
    cipher_vecs = []
    for v in vecs:
        c = matrix_mul_3(key_matrix, v)
        cipher_vecs.append(c)
    return vectors_to_text(cipher_vecs)

def hill_decrypt(ciphertext, key_matrix):
    inv = matrix_inv_3(key_matrix)
    if inv is None:
        raise ValueError("Hill matrix not invertible")
    vecs = text_to_vectors(ciphertext)
    plain_vecs = []
    for v in vecs:
        p = matrix_mul_3(inv, v)
        plain_vecs.append(p)
    return vectors_to_text(plain_vecs)

# ---------------- Combined ----------------
def combined_encrypt(plaintext, playfair_key, hill_key_str):
    pf_cipher = playfair_encrypt(plaintext, playfair_key)
    hill_key = derive_hill_matrix_from_key(hill_key_str)
    final_cipher = hill_encrypt(pf_cipher, hill_key)
    return final_cipher, pf_cipher, hill_key

def combined_decrypt(ciphertext, playfair_key, hill_key_matrix):
    after_hill = hill_decrypt(ciphertext, hill_key_matrix)
    plaintext = playfair_decrypt(after_hill, playfair_key)
    return plaintext, after_hill

# ---------------- Known-plaintext Hill recovery ----------------
def recover_hill_from_known_pairs(plain_after_playfair, cipher_after_hill):
    P = sanitize_text(plain_after_playfair)
    C = sanitize_text(cipher_after_hill)
    if len(P) < 9 or len(C) < 9:
        raise ValueError("Need at least 3 blocks (9 letters) of known plaintext->ciphertext to recover 3x3 Hill matrix.")
    Pmat = [[0]*3 for _ in range(3)]
    Cmat = [[0]*3 for _ in range(3)]
    for col in range(3):
        chunkP = P[3*col:3*col+3]
        chunkC = C[3*col:3*col+3]
        for row in range(3):
            Pmat[row][col] = (ord(chunkP[row]) - 65) % MOD
            Cmat[row][col] = (ord(chunkC[row]) - 65) % MOD
    invP = matrix_inv_3(Pmat)
    if invP is None:
        raise ValueError("Known plaintext matrix not invertible mod26; need different block selection.")
    M = matrix_mul_3(Cmat, invP)
    return M

# ---------------- Playfair breaker (hill-climb) ----------------
COMMON_WORDS = ["THE","AND","TO","OF","IN","IS","YOU","THAT","IT","HE","FOR","WAS","ON","ARE","AS","WITH","HIS","THEY","I"]

def score_plaintext(text):
    s = 0
    T = text.upper()
    for w in COMMON_WORDS:
        s += 12 * T.count(w)
    freq = Counter(T)
    vowel_count = sum(freq.get(ch,0) for ch in "AEIOU")
    s += vowel_count * 0.6
    for dg in ["TH","HE","IN","ER","AN","RE","ED","ON","ES","EN","AT","TE","OR","TI","HI"]:
        s += 2 * T.count(dg)
    return s

def random_playfair_perm():
    letters = list(ALPHABET)
    random.shuffle(letters)
    return "".join(letters)

def decrypt_with_perm(ciphertext, perm25):
    table = list(perm25)
    pos = {table[i]: (i//5, i%5) for i in range(25)}
    pairs = [ciphertext[i:i+2] for i in range(0,len(ciphertext),2)]
    plain = []
    for a,b in pairs:
        ra, ca = pos[a]
        rb, cb = pos[b]
        if ra == rb:
            plain.append(table[ra*5 + ((ca-1)%5)] + table[rb*5 + ((cb-1)%5)])
        elif ca == cb:
            plain.append(table[((ra-1)%5)*5 + ca] + table[((rb-1)%5)*5 + cb])
        else:
            plain.append(table[ra*5 + cb] + table[rb*5 + ca])
    return "".join(plain)

def playfair_hill_climb_break(cipher_after_hill, iterations=5000, restarts=5):
    best_overall = ("", "", -1)
    for r in range(restarts):
        best_key = random_playfair_perm()
        best_plain = decrypt_with_perm(cipher_after_hill, best_key)
        best_score = score_plaintext(best_plain)
        for it in range(iterations):
            a,b = random.sample(range(25),2)
            klist = list(best_key)
            klist[a], klist[b] = klist[b], klist[a]
            cand_key = "".join(klist)
            cand_plain = decrypt_with_perm(cipher_after_hill, cand_key)
            cand_score = score_plaintext(cand_plain)
            # accept if better or small probabilistic escape
            if cand_score > best_score or random.random() < 0.001:
                best_key, best_score, best_plain = cand_key, cand_score, cand_plain
        if best_score > best_overall[2]:
            best_overall = (best_key, best_plain, best_score)
    return {"perm": best_overall[0], "plain": best_overall[1], "score": best_overall[2]}

# ---------------- Frequency analysis ----------------
ENGLISH_FREQ = {
 'A': 8.17, 'B': 1.49, 'C': 2.78, 'D': 4.25, 'E': 12.70, 'F': 2.23,
 'G': 2.02, 'H': 6.09, 'I': 6.97, 'J': 0.15, 'K': 0.77, 'L': 4.03,
 'M': 2.41, 'N': 6.75, 'O': 7.51, 'P': 1.93, 'Q': 0.10, 'R': 5.99,
 'S': 6.33, 'T': 9.06, 'U': 2.76, 'V': 0.98, 'W': 2.36, 'X': 0.15,
 'Y': 1.97, 'Z': 0.07
}

def frequency_report(text):
    s = sanitize_text(text)
    n = len(s)
    freq = Counter(s)
    report = {ch: (freq.get(ch,0), (freq.get(ch,0)/n*100) if n>0 else 0.0) for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ"}
    # compute chi-square against English frequencies for monoalphabetic check
    chi = 0.0
    for ch in "ABCDEFGHIJKLMNOPQRSTUVWXYZ":
        observed = report[ch][0]
        expected = ENGLISH_FREQ.get(ch,0)/100.0 * n
        if expected > 0:
            chi += ((observed - expected)**2) / expected
    return {"length": n, "counts": report, "chi2": chi}

# ---------------- Simulation wrapper ----------------
def simulate_and_attack(plaintext, playfair_key, hill_key_str, known_blocks=3, climb_iters=3000):
    out = {}
    start = time.time()
    final_cipher, pf_cipher, hill_key = combined_encrypt(plaintext, playfair_key, hill_key_str)
    out["plaintext_sanitized"] = sanitize_text(plaintext)
    out["after_playfair"] = pf_cipher
    out["final_cipher"] = final_cipher
    out["hill_key_matrix"] = hill_key

    # Frequency report of final ciphertext
    out["freq_report_final"] = frequency_report(final_cipher)

    # Known-plaintext attack on Hill (assume attacker knows first known_blocks blocks AFTER Playfair)
    try:
        letters_needed = known_blocks*3
        known_pf = pf_cipher[:letters_needed]
        known_final = final_cipher[:letters_needed]
        recovered_hill = recover_hill_from_known_pairs(known_pf, known_final)
        out["recovered_hill"] = recovered_hill
        after_hill_decrypted = hill_decrypt(final_cipher, recovered_hill)
        out["after_hill_decrypted_full"] = after_hill_decrypted
    except Exception as e:
        out["recovery_error"] = str(e)
        return out

    # Attempt Playfair break (only if long enough)
    cleaned_after_hill = sanitize_text(after_hill_decrypted).replace("J","I")
    if len(cleaned_after_hill) < 30:
        out["playfair_breaker_note"] = "Too short for reliable Playfair breaking (<30 letters)."
        # still attempt quick hill-climb with small iterations
        attempt = playfair_hill_climb_break(cleaned_after_hill, iterations=500, restarts=3)
    else:
        attempt = playfair_hill_climb_break(cleaned_after_hill, iterations=climb_iters, restarts=5)
    out["playfair_breaker"] = attempt
    # Decrypt candidate using guessed perm (try to map perm to table then decrypt with inferred key)
    # attempt['plain'] is the candidate plaintext
    out["recovered_plain_candidate"] = clean_playfair_plain(attempt["plain"])
    # Also include direct decryption with real Playfair key for comparison (if available)
    real_pf_decryption = playfair_decrypt(after_hill_decrypted, playfair_key)
    out["decrypted_with_true_key"] = real_pf_decryption
    out["decrypted_with_true_key_cleaned"] = clean_playfair_plain(real_pf_decryption)
    out["time_elapsed"] = time.time() - start
    return out

# ---------------- Experiment runner ----------------
def experiment_vary_length(base_plaintext, playfair_key, hill_key_str, lengths=[60,120,240], trials=3):
    results = []
    for L in lengths:
        success_count = 0
        times = []
        for t in range(trials):
            # produce plaintext of length L (by repeating base)
            p = (base_plaintext * ((L // len(base_plaintext)) + 2))[:L]
            res = simulate_and_attack(p, playfair_key, hill_key_str, known_blocks=3, climb_iters=2000)
            times.append(res.get("time_elapsed", None))
            # success heuristics: recovered Hill equals original (matrix equal) AND Playfair cleaned match
            hill_ok = "recovered_hill" in res and res["recovered_hill"] == res["hill_key_matrix"]
            plain_ok = False
            if "decrypted_with_true_key_cleaned" in res and "recovered_plain_candidate" in res:
                # compare cleaned strings for equality or high overlap
                a = res["decrypted_with_true_key_cleaned"]
                b = res["recovered_plain_candidate"]
                # consider success if a is substring of b or vice versa OR Levenshtein similarity high
                if a == b or a in b or b in a:
                    plain_ok = True
            if hill_ok and plain_ok:
                success_count += 1
        results.append({"length": L, "trials": trials, "successes": success_count, "avg_time": sum([x for x in times if x])/len(times)})
    return results

# ---------------- Main demo ----------------
if __name__ == "__main__":
    pp = pprint.PrettyPrinter(indent=2)
    # Set keys and plaintext according to assignment requirement:
    playfair_key = "SECURITYKEY"   # >=10 chars as required
    hill_key_str = "CRYPTOGRAPHY"  # will use first 9 letters -> 3x3 matrix
    plaintext = ("THIS IS A SECRET MESSAGE FOR THE CT 486 CLASS. PLEASE REVIEW THE DESIGN AND ATTACK. "
                 "WE ARE TESTING THE COMBINED PLAYFAIR AND HILL CIPHER IMPLEMENTATION.")
    plaintext = sanitize_text(plaintext)

    print("\n=== Encryption / Decryption Demo ===")
    final_cipher, pf_cipher, hill_key = combined_encrypt(plaintext, playfair_key, hill_key_str)
    print("Plaintext (sanitized):", plaintext)
    print("After Playfair (stage1):", pf_cipher)
    print("Final Cipher (stage2 Hill):", final_cipher)
    recovered_plain, after_hill = combined_decrypt(final_cipher, playfair_key, hill_key)
    print("Recovered (raw) plaintext (may include filler):", recovered_plain)
    print("Recovered (cleaned) plaintext:", clean_playfair_plain(recovered_plain))

    print("\n=== Attack Simulation (known-plaintext & Playfair breaker) ===")
    sim = simulate_and_attack(plaintext, playfair_key, hill_key_str, known_blocks=3, climb_iters=3000)
    print("Time elapsed (s):", sim.get("time_elapsed"))
    print("\n-- Hill key matrix used (original):")
    for row in sim.get("hill_key_matrix", []):
        print(row)
    print("\n-- Recovered Hill matrix (attacker):")
    if "recovered_hill" in sim:
        for row in sim["recovered_hill"]:
            print(row)
    else:
        print("No recovered Hill (error):", sim.get("recovery_error"))

    print("\n-- After Hill decrypted sample (this is Playfair-stage ciphertext):")
    print(sim.get("after_hill_decrypted_full", "")[:200])

    print("\n-- Frequency analysis of final ciphertext (chi-square):")
    freq = sim.get("freq_report_final", {})
    print("Length:", freq.get("length"))
    print("Chi-square:", freq.get("chi2"))
    # top letter frequencies
    counts = freq.get("counts", {})
    top = sorted(counts.items(), key=lambda x: -x[1][0])[:10]
    print("Top letter counts (letter: count, %):")
    for ch,(cnt,perc) in top:
        print(f" {ch}: {cnt}, {perc:.2f}%")

    print("\n-- Playfair breaker candidate (best):")
    pb = sim.get("playfair_breaker", {})
    print("Score:", pb.get("score"))
    print("Candidate plaintext (raw):", pb.get("plain", "")[:400])
    print("Candidate plaintext (cleaned):", sim.get("recovered_plain_candidate", "")[:400])

    print("\n-- Decrypted with TRUE Playfair key (for verification):")
    print("Raw:", sim.get("decrypted_with_true_key", "")[:400])
    print("Cleaned:", sim.get("decrypted_with_true_key_cleaned", "")[:400])

    print("\n=== Experiment: success vs length (quick) ===")
    base = "THISISASECRETMESSAGE"
    explen = [60, 120, 240]
    exp = experiment_vary_length(base, playfair_key, hill_key_str, lengths=explen, trials=2)
    pp.pprint(exp)
