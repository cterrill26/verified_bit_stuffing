import exrex
import argparse

def valid_message_segment(b, k, s):
    if len(b) <= len(k):
        return True
    elif b.startswith(k):
        return b[len(k)] == s and valid_message_segment(b[len(k)+1:], k, s)
    else:
        return valid_message_segment(b[1:], k, s)

def valid_message_end(b, k, s):
    if len(b) < len(k):
        return True
    elif b.startswith(k):
        if len(b) == len(k):
            return False
        else:
            return b[len(k)] == s and valid_message_end(b[len(k)+1:], k, s)
    else:
        return valid_message_end(b[1:], k, s)

def no_flag_in_data(f, k, s):
    for i in range(len(k)+1):
        if valid_message_segment(k[0:i] + f, k, s):
            return False
    return True

def no_flag_overlapping_real_flag(f, k, s):
    for i in range(1,len(f)):
        if f[0:i] == f[-i:]:
            for j in range(len(k)+1):
                if valid_message_end(k[0:j] + f[0:-i], k, s):
                    return False
    return True

def valid_protocol(f, k, s):
    return no_flag_in_data(f, k, s) and no_flag_overlapping_real_flag(f, k, s)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--flag", help="flag bits", required=True)
    parser.add_argument("-k", "--kernel", help="bit pattern after which to stuff", required=True)
    parser.add_argument("-s", "--stuff", help="stuffing bit", required=True)
    args = parser.parse_args()

    flags = list(exrex.generate(args.flag.replace(".", "[01]")))
    kernels = list(exrex.generate(args.kernel.replace(".", "[01]")))
    stuffs = list(exrex.generate(args.stuff.replace(".", "[01]")))

    for f in flags:
        for k in kernels:
            for s in stuffs:
                assert(0 < len(k) < len(f) and len(s) == 1)
                assert(all(c in "01" for c in f))
                assert(all(c in "01" for c in k))
                assert(all(c in "01" for c in s))

                if valid_protocol(f, k, s):
                    print("Flag: " + f + " Kernel: " + k + " Stuff: " + s)
