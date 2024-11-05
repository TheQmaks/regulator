import re
import string
import logging
import argparse

from typing import List, Set, Dict
from itertools import combinations_with_replacement

import tldextract
import editdistance

from dank.DankEncoder import DankEncoder
from dank.DankGenerator import DankGenerator


MEMO = {}
LOGFILE_NAME = 'logs/regulator.log'
DNS_CHARS = string.ascii_lowercase + string.digits + '._-'


def edit_closures(items: List[str], delta: int = 5) -> List[Set[str]]:
    """computes all subsets of items bounded by fixed edit distance"""
    global MEMO
    ret = []
    for a in items:
        found = False
        r = set([a])
        for b in items:
            dist = MEMO[a + b] if a + b in MEMO else MEMO[b + a]
            if dist < delta:
                r.add(b)
        for s in ret:
            if r == s:
                found = True
                break
        if not found:
            ret.append(r)
    return ret


def tokenize(items: List[str]):
    """tokenize DNS hostnames into leveled word tokens"""
    ret = []
    hosts = []
    for item in items:
        t = tldextract.extract(item)
        hosts.append(t.subdomain)
    labels = [host.split('.') for host in hosts]
    for label in labels:
        n = []
        for item in label:
            t = []
            tokens = [f'-{e}' if i != 0 else e for i, e in enumerate(item.split('-'))]
            for token in tokens:
                subtokens = [x for x in re.split('([0-9]+)', token) if len(x) > 0]
                for i in range(len(subtokens)):
                    if subtokens[i] == '-' and i + 1 < len(subtokens):
                        subtokens[i + 1] = ('-' + subtokens[i + 1])
                    else:
                        t.append(subtokens[i])
            n.append(t)
        ret.append(n)
    return ret


def compress_number_ranges(regex: str) -> str:
    """given an 'uncompressed' regex, returns a regex with ranges instead"""
    ret = regex[:]
    stack, groups, repl, extra, hyphen = [], [], {}, {}, {}
    for i, e in enumerate(regex):
        if e == '(':
            stack.append(i)
        elif e == ')':
            start = stack.pop()
            group = regex[start + 1:i]
            tokens = group.split('|')
            numbers = [token for token in tokens if token.isnumeric()]
            nonnumbers = [token for token in tokens if not token.isnumeric() and not re.match('-[0-9]+', token)]
            hyphenatednumbers = [token[1:] for token in tokens if re.match('-[0-9]+', token)]
            if '?' in group or ')' in group or '(' in group:
                continue
            elif len(numbers) != 0 and len(hyphenatednumbers) != 0:
                continue
            elif len(numbers) > 1:
                g1 = '|'.join(numbers)
                g2 = '|'.join(nonnumbers)
                repl[g1] = group
                extra[g1] = g2
                groups.append(g1)
            elif len(hyphenatednumbers) > 1:
                g1 = '|'.join(hyphenatednumbers)
                g2 = '|'.join(nonnumbers)
                repl[g1] = group
                extra[g1] = g2
                groups.append(g1)
                hyphen[g1] = True
    for group in groups:
        generalized = '(' if not group in hyphen else '(-'
        positions = {}
        tokens = [g[::-1] for g in group.split('|')]
        for token in tokens:
            for position, symbol in enumerate(token):
                if not position in positions:
                    positions[position] = set([])
                positions[position].add(int(symbol))
        s = sorted(tokens, key=lambda x: len(x))
        start, end = len(s[-1]) - 1, len(s[0]) - 1
        for i in range(start, end, -1):
            positions[i].add(None)
        for i, symbols in sorted(positions.items(), key=lambda x: x[0], reverse=True):
            optional = None in symbols
            if optional:
                symbols.remove(None)
            s = sorted(symbols)
            start, end = s[0], s[-1]
            if start != end:
                generalized += f'[{start}-{end}]{"?" if optional else ""}'
            else:
                generalized += f'{start}{"?" if optional else ""}'
        generalized += ')'
        ext = extra[group]
        rep = repl[group]
        if ext != '':
            generalized = f'({generalized}|({ext}))'
        ret = ret.replace(f'({rep})', generalized)
    return ret


def closure_to_regex(domain: str, members: List[str]) -> str:
    """converts edit closure to a regular language"""
    ret, levels, optional = '', {}, {}
    tokens = tokenize(members)
    for member in tokens:
        for i, level in enumerate(member):
            if i not in levels:
                levels[i] = {}
                optional[i] = {}
            for j, token in enumerate(level):
                if not j in levels[i]:
                    levels[i][j] = set([])
                    optional[i][j] = []
                levels[i][j].add(token)
                optional[i][j].append(token)
    for i, level in enumerate(levels):
        n = '(.' if i != 0 else ''
        for j, position in enumerate(levels[level]):
            k = len(levels[level][position])
            if i == 0 and j == 0:
                n += f"({'|'.join(levels[level][position])})"
            elif k == 1 and j == 0:
                n += f"{'|'.join(levels[level][position])}"
            else:
                isoptional = len(optional[level][position]) != len(members)
                n += f"({'|'.join(levels[level][position])}){'?' if isoptional else ''}"
        values = list(map(lambda x: ''.join(x), zip(*optional[level].values())))
        isoptional = len(set(values)) != 1 or len(values) != len(members)
        ret += (n + ")?" if isoptional else n + ")") if i != 0 else n
    return compress_number_ranges(f'{ret}.{domain}')


def is_good_rule(regex: str, nkeys: int, threshold: int, max_ratio: float) -> bool:
    """applies ratio test to determine if a rule is acceptable"""
    e = DankEncoder(regex, 256)
    nwords = e.num_words(1, 256)
    return nwords < threshold or (nwords / nkeys) < max_ratio


def sort_and_unique(file_name: str):
    with open(file_name, "r") as file:
        data = file.readlines()
        data = sorted(set(data))
    with open(file_name, "w") as file:
        file.writelines(data)


def main():
    global DNS_CHARS, MEMO

    logging.basicConfig(format='%(asctime)-15s - %(name)s - %(levelname)s - %(message)s', level=logging.INFO, filename=LOGFILE_NAME, filemode='a')
    parser = argparse.ArgumentParser(description='DNS Regulator')
    parser.add_argument('-th', '--threshold', required=False, type=int, default=500, help='Threshold to start performing ratio test')
    parser.add_argument('-mr', '--max-ratio', required=False, type=float, default=25.0, help='Ratio test parameter R: len(Synth)/len(Obs) < R')
    parser.add_argument('-ml', '--max-length', required=False, type=int, default=1000, help='Maximum rule length for global search')
    parser.add_argument('-dl', '--dist-low', required=False, type=int, default=2, help='Lower bound on string edit distance range')
    parser.add_argument('-dh', '--dist-high', required=False, type=int, default=10, help='Upper bound on string edit distance range')
    parser.add_argument('-t', '--target', required=True, type=str, help='The domain to target')
    parser.add_argument('-f', '--hosts', required=True, type=str, help='The observed hosts file')
    parser.add_argument('-o', '--output', required=False, type=str, help='Output filename (default: output)', default="output")
    args = vars(parser.parse_args())

    logging.info(f'REGULATOR starting: MAX_RATIO={args["max_ratio"]}, THRESHOLD={args["threshold"]}')

    known_hosts, new_rules = set([]), set([])
    trie = {}

    def add_to_trie(trie: Dict, item: str):
        node = trie
        for char in item:
            if char not in node:
                node[char] = {}
            node = node[char]
        node['$'] = True  # Mark the end of a valid hostname

    def search_trie(trie: Dict, prefix: str):
        node = trie
        for char in prefix:
            if char not in node:
                return []
            node = node[char]
        return collect_trie_keys(node, prefix)

    def collect_trie_keys(node: Dict, prefix: str):
        keys = []
        if '$' in node:
            keys.append(prefix)
        for char, child in node.items():
            if char != '$':
                keys.extend(collect_trie_keys(child, prefix + char))
        return keys

    with open(args['hosts'], 'r') as handle:
        known_hosts = sorted(list(set([line.strip() for line in handle.readlines()])))
        for host in known_hosts:
            if host != args['target']:
                tokens = tokenize([host])
                if len(tokens) > 0 and len(tokens[0]) > 0 and len(tokens[0][0]) > 0:
                    add_to_trie(trie, host)
                else:
                    logging.warning(f'Rejecting malformed input: {host}')
                    known_hosts.remove(host)

    logging.info(f'Loaded {len(known_hosts)} observations')
    logging.info('Building table of all pairwise distances...')

    for s, t in combinations_with_replacement(known_hosts, 2):
        MEMO[s + t] = editdistance.eval(s, t)

    logging.info('Table building complete')

    for k in range(args['dist_low'], args['dist_high']):
        logging.info(f'k={k}')
        closures = edit_closures(known_hosts, delta=k)
        for closure in closures:
            if len(closure) > 1:
                r = closure_to_regex(args['target'], closure)
                if len(r) > args['max_length']:
                    continue
                if r not in new_rules and is_good_rule(r, len(closure), args['threshold'], args['max_ratio']):
                    new_rules.add(r)

    ngrams = sorted(list(set(DNS_CHARS) | set([''.join([i, j]) for i in DNS_CHARS for j in DNS_CHARS])))
    for ngram in ngrams:
        keys = search_trie(trie, ngram)
        if len(keys) == 0:
            continue

        r = closure_to_regex(args['target'], keys)
        if r not in new_rules and is_good_rule(r, len(keys), args['threshold'], args['max_ratio']):
            new_rules.add(r)

        last, prefixes = None, sorted(list(set([tokenize([k])[0][0][0] for k in search_trie(trie, ngram)])))
        for prefix in prefixes:
            logging.info(f'Prefix={prefix}')
            keys = search_trie(trie, prefix)

            r = closure_to_regex(args['target'], keys)
            if r not in new_rules and is_good_rule(r, len(keys), args['threshold'], args['max_ratio']):
                if last is None or not prefix.startswith(last):
                    last = prefix
                else:
                    logging.warning(f"Rejecting redundant prefix: {prefix}")
                    continue
                new_rules.add(r)

            if len(prefix) > 1:
                for k in range(args['dist_low'], args['dist_high']):
                    closures = edit_closures(keys, delta=k)
                    for closure in closures:
                        r = closure_to_regex(args['target'], closure)
                        if r not in new_rules and is_good_rule(r, len(closure), args['threshold'], args['max_ratio']):
                            new_rules.add(r)
                        elif r not in new_rules:
                            logging.error(f'Rule cannot be processed: {r}')

    with open(f"{args['target']}.rules", 'w') as handle:
        for rule in new_rules:
            handle.write(f'{rule}\n')

    with open(args['output'], 'w') as handle:
        for line in new_rules:
            for item in DankGenerator(line.strip()):
                handle.write(item.decode('utf-8') + '\n')

    sort_and_unique(args['output'])

    with open(args['output'], 'r+') as handle:
        replaced = sorted(set(map(lambda line: re.sub('\.{2,}', '.', line), handle.readlines())))
    with open(args['output'], 'w') as handle:
        handle.writelines(replaced)


if __name__ == '__main__':
    main()
