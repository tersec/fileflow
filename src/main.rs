/*
 * Why not tree edit distance:
 * (1) weighted version is O(n^3) for optimality, and notably, non-pathological
 *     directory trees don't typically contain as many directorie as files, and
 *     this exploits this. of course, one can imagine reductions to TED where a
 *     directory-only set of ndoes is presented to a TED algorithm but see (2).
 *
 * (2) doesn't map on to problem easily as stated
 *   (2a) "relabel" is .. not especially interesting.
 *   (2b) part of point is to leverage cp -r, rm -r, and mv on whole treees
 *        to help illustrate things. usual insert/relabel/delete node not a
 *        useful abstraction here.
 *   (2c) because the "cost" in understanding of one of these recursive calls is
 *        constant in human terms, and the point is to optimize for that there's
 *        no constant-multiplier for weights to reduce this to the per-node cost
 *        sets used in usual TED algorithms.
 *   (2d) relabeling makes more sense for directory names but in terms of human
 *        understanding, mv dir_name_0 dir_name_1 comprehensible enough that it
 *        isn't especially worth trying to target for minimizing an edit script
 *   (2e) one fundamental disconnect is that in some sense, there are "infinite"
 *        cost inserts (of previously unknown files), because the tree here's an
 *        indirect set of pointers to actual file contents, i.e. metadata and is
 *        not something self-sufficient.
 *
 *  (3) isn't the end goal anyway. purpose isn't to mechanically transform one
 *      file/dir tree to another, but to understand qualitatively what changed
 *      between them. it's descriptive, not mechanistic.
 *
 *  (4) part of what distinguishes a real global TED algorithm is that it's a
 *      global optimization, but that also means that working as designed, it
 *      might find some unexpected way to save a few edits by intermingling a
 *      group of mostly unrelated directories. This approach is more readable
 *      because it is a clean mapping from source to destination directories,
 *      and to understand each requires only local knowledge, not tracking an
 *      unbounded set of potential edits through an entire tree.
 *
 *      conceptually, this isn't aimed at creating an in-place editing script
 *      but rather something like a mapping function from the immutable input
 *      to a specified output directory/file structure.
 *
 *  In summary, TED, despite its extensive literature, isn't the most useful
 *  problem to map this onto, for the purpose this describes.
 *
 * Why not simply lean on git? Lack of directory structure discovery and
 * inefficient treatment of file copying.
 */

 /*
  * Other TODO notes:
  * - multiple input/multiple output is another use case for matching hashes
  *   rather than TED; TED can handle this more synthetic case, but, largely
  *   isn't designed to;
  *
  * - this decreases the MH-Diff paper's section on unintuitive intermediate
  *   steps (mass-group-files for moving, then move, etc) to less relevance,
  *   because the question being answered isn't, exactly, the exact sequence
  *   of moves (which is nice but not 100% required) but bitrot detction, so
  *   full TED mechanism might even be counterproductive for reasons noted;
  *
  * - might be worth having separate mode (or just document) effect of src and
  *   dest flipping, because in some ways new content is irrelevant, but files
  *   which have vanished are relevant. basically a UX issue but worth framing
  *   output maybe not in "added"/"removed" but comm(1)-like terms of which of
  *   the inputs has which content;
  *
  * - separately note small, more traditional TED-like things such as timestamp
  *   and filename changes. These are strictly subsidiary, unlike with true TED
  *   algorithms, for reasons which are application/domain specific.
  *
  * - https://difftastic.wilfred.me.uk/tricky_cases.html and
  *   https://difftastic.wilfred.me.uk/tree_diffing.html useful as references
  *   summarizing approaches, from the tree diffing side. MH-Diff seems among
  *   the most promising, but sdiff itself just skips the interesting cases
  */

use std::cmp::min;
use std::collections::HashMap;
use std::collections::HashSet;
use std::env;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::mem::size_of;
use std::time::Instant;

// TODO benchmark u128 vs u64
// https://doc.rust-lang.org/std/primitive.u128.html

// TODO currently implicitly, but use something like this systematically
type FileHashInfo = String;

type DirPath = Vec<String>;
type HashBitmapLimb = u128;
type HashBitmap = Vec<HashBitmapLimb>;
type FileSet = HashBitmap;
type HashTree = HashMap<DirPath, FileSet>;
type HashIndex = HashMap<String, HashSet<DirPath>>;
type CommonHashIndex = HashMap<String, usize>;
type ParsedLines = Vec<(String, Vec<String>)>;

const ONE: u128 = 1u128;

const LIMB_BITS: usize = size_of::<HashBitmapLimb>() * 8;
// TODO can use compile-time code here?
// TODO error: non-item macro in item position: assert
// assert!(LIMB_BITS == 64);

// operations on HashBitmap
fn get_empty_hash_bitmap(common_hashes: &CommonHashIndex) -> HashBitmap {
    // TODO can sanity-check common hash index because indices should be all ints
    // in range
    // TODO can do this more efficiently, e.g., as part of creation?
    let mut v: HashBitmap = Vec::new();
    v.resize((common_hashes.len() + LIMB_BITS - 1) / LIMB_BITS, 0);
    return v;
}

fn card(x: &HashBitmap) -> u32 {
    let mut res = 0u32;
    for leaf in x {
        res += leaf.count_ones();
    }
    res
}

fn both_diff_len(x: &HashBitmap, y: &HashBitmap) -> (u32, u32) {
    assert!(x.len() == y.len());
    let mut res = (0u32, 0u32);
    for i in 0..x.len() {
        res.0 += (x[i] & !y[i]).count_ones();
        res.1 += (y[i] & !x[i]).count_ones();
    }
    res
}

fn add_hash_bitmaps(x: &HashBitmap, y: &HashBitmap) -> HashBitmap {
    if x.len() == 0 {
        // TODO is there a way to special-case these?
        // avoid copies etc when not necessary
        // or bigger refactor
        return y.to_vec();
    }
    if y.len() == 0 {
        return x.to_vec();
    }

    assert!(x.len() == y.len());
    let mut x = x.clone();
    for i in 0..x.len() {
        x[i] |= y[i];
    }
    x
}

fn sub_hash_bitmaps(x: &HashBitmap, y: &HashBitmap) -> HashBitmap {
    // TODO FIXME horrible, it's because of default value in search func,
    // so instead make search func use reasonable default value
    if y.len() == 0 || x.len() == 0 {
        // TODO same issue as add_hash_bitmaps -- this should be no-op/free
        return x.to_vec();
    }

    assert!(x.len() == y.len());
    let mut x = x.clone();
    for i in 0..x.len() {
        x[i] = x[i] & !y[i];
    }
    x
}

fn set_bit(x: &mut HashBitmap, i: usize) {
    let leaf_pos = i / LIMB_BITS;
    let leaf_idx = i % LIMB_BITS;
    x[leaf_pos] |= ONE << leaf_idx;
}

// TODO this was/should be an iterator
fn get_set_bits(x: &HashBitmap) -> Vec<usize> {
    let mut res: Vec<usize> = Vec::new();
    for i in 0..x.len() {
        let leaf = x[i];
        for j in 0..LIMB_BITS {
            if (leaf & (ONE << j)) != 0 {
                res.push(i * LIMB_BITS + j);
            }
        }
    }
    res
}

// Parsing
fn parse_line(line: &str) -> Option<(String, Vec<&str>)> {
    match line.split_once(" ") {
        Some((hash_info, path_str)) => Some((
            hash_info.to_string(),
            path_str.trim_start().split("/").collect::<Vec<_>>(),
        )),
        None => None,
    }
}

fn parse_file(filename: &str) -> ParsedLines {
    // TODO use io:Result<()> and let file = File::open("foo.txt")?;
    // these nested match {}s are the main stylistic thing that bugs me in
    // Rust currently and there's obviously solutions to it
    match File::open(filename) {
        Ok(file) => {
            let reader = BufReader::new(file);
            reader
                .lines()
                .filter_map(|maybe_line| match maybe_line {
                    Ok(line) => match parse_line(&line) {
                        Some((hash_info, path)) => Some((
                            hash_info,
                            path.iter().map(|&s| s.to_string()).collect::<Vec<_>>(),
                        )),
                        None => None,
                    },
                    Err(_) => None,
                })
                .collect::<Vec<_>>()
        }
        Err(_) => Vec::new(), // TODO too silent
    }
}

fn get_common_hashes(l0: &ParsedLines, l1: &ParsedLines) -> (Vec<String>, CommonHashIndex) {
    let mut chi: CommonHashIndex = HashMap::new();
    let mut ich: Vec<String> = Vec::new();
    let l1hs: HashSet<FileHashInfo> = l1.iter().map(|(hash_info, _)| hash_info.clone()).collect();
    for (fhi, _) in l0 {
        if l1hs.contains(fhi) && !chi.contains_key(fhi) {
            let i = chi.len();
            chi.insert(fhi.clone(), i);
            ich.push(fhi.clone());
            assert!(ich.len() == chi.len());
        }
    }
    // can do round-trip internal consistency checks here
    (ich, chi)
}

fn is_path_prefix(p0: &DirPath, p1: &DirPath) -> bool {
    // Operates bidirectionally with regards to whether p0 is a prefix of p1 or
    // vice-versa.
    // allIt(0 ..< min(p0.len(), p1.len()), p0[it] == p1[it])
    for i in 0..min(p0.len(), p1.len()) {
        if p0[i] != p1[i] {
            return false;
        }
    }
    return true;
}

fn build_source_tree(
    parsed_lines: &ParsedLines,
    common_hashes: &CommonHashIndex,
) -> (HashTree, HashIndex, HashIndex) {
    let mut hash_tree: HashTree = HashMap::new();
    let mut hash_index_dirs: HashIndex = HashMap::with_capacity(parsed_lines.len());
    let mut hash_index_files: HashIndex = HashMap::with_capacity(parsed_lines.len());

    for line in parsed_lines {
        let hash_info = &line.0;
        // Files that are either added in or removed aren't relevant in terms of
        // analyzing changes in tree structure.
        let common_hash_index = match common_hashes.get(hash_info) {
            Some(idx) => idx,
            None => {
                continue;
            }
        };

        // Useful to display results, but not much used in algorithm
        if hash_index_files.contains_key(hash_info) {
            // why doesn't entry() take a reference? I guess because of methods
            // such as `or_insert`, but what if I just want to modify, only?
            hash_index_files.entry(line.0.clone()).and_modify(|ps| {
                ps.insert(line.1.clone());
            });
        } else {
            let mut new_set: HashSet<DirPath> = HashSet::new();
            new_set.insert(line.1.clone());
            hash_index_files.insert(line.0.clone(), new_set);
        }

        for i in 0..(line.1.len() - 1) {
            let mut dir_path: Vec<String> = Vec::new();
            dir_path.extend_from_slice(&(line.1)[0..(i + 1)]);
            assert!(dir_path.len() > 0);

            if !hash_tree.contains_key(&dir_path) {
                let mut new = get_empty_hash_bitmap(&common_hashes);
                set_bit(&mut new, *common_hash_index);
                hash_tree.insert(dir_path.clone(), new);
            } else {
                hash_tree
                    .entry(dir_path.clone())
                    .and_modify(|e| set_bit(e, *common_hash_index));
            }

            // Two tables should be mutually consistent, TODO can check this
            // TODO what are assumptions about inconsistent/repeated/etc paths?
            // because could just use Vecs
            if hash_index_dirs.contains_key(hash_info) {
                hash_index_dirs.entry(hash_info.clone()).and_modify(|e| {
                    e.insert(dir_path);
                });
            } else {
                let mut new_set: HashSet<DirPath> = HashSet::new();
                new_set.insert(dir_path);
                hash_index_dirs.insert(hash_info.to_string(), new_set);
            }
        }
    }

    (hash_tree, hash_index_dirs, hash_index_files)
}

fn get_possible_source_paths(
    hash_index: &HashIndex,
    common_files: &Vec<String>,
    file_set: &FileSet,
) -> Vec<DirPath> {
    let mut paths: HashSet<DirPath> = HashSet::new();
    for i in get_set_bits(file_set) {
        hash_index[&common_files[i]].iter().for_each(|dir_path| {
            paths.insert(dir_path.clone());
        });
    }

    // brute force re clone()
    paths.iter().map(|e| e.clone()).collect::<Vec<_>>()
}

fn format_dirpath(p: &DirPath) -> String {
    let mut s: String = String::from("");
    for n in p.iter() {
        s.push_str("/");
        s.push_str(n);
    }
    s
}

fn brute_force_find_best_match(
    dest_hashes: &FileSet,
    source_path_cards: &HashMap<DirPath, u32>,
    accum_source_hashes: &FileSet,
    source_tree: &HashTree,
    //possible_source_paths: &Vec<DirPath>,
    possible_source_paths: &[DirPath],
    max_depth: u32,
) -> (Vec<DirPath>, u32, FileSet) {
    // there might not be any existing directory,
    // e.g., if it's a random mix of files from source dirs
    // Symmetric difference between dest_hashes
    let mut best_score = card(dest_hashes);

    // bestPaths here ignores ancestors; they'll be taken into accounts on
    // returning. As such, this isn't tail-call or CPS-friendly, but it is
    // designed for relatively shallow trees such as directory structures.
    let mut best_paths: Vec<DirPath> = Vec::new();
    let mut best_file_set: FileSet = Vec::new();

    for (source_path_idx, source_path) in possible_source_paths.iter().enumerate() {
        let candidate_tree = &source_tree[source_path];
        // Overlaying/overlapping directory contents is subtle, and, e.g., order
        // starts mattering. With 3 or 4 directories, might become less obvious,
        // in terms of understandable output. That it's not attempting to create
        // an edit script might ameliorate this though, as it can illustrate how
        // a destinction directory's the sum, in effect, of multiple others.
        const COST_PER_DIRECTORY: u32 = 0;

        // "rm" and "cp" are the same weight for this purpose -- approximately as
        // easy to understand.
        let (undershoot, overshoot) = both_diff_len(dest_hashes, candidate_tree);

        // TODO recreate the maybe_update_best_match template
        // @[sourcePath], undershoot + overshoot, candidateTree[])
        if (undershoot + overshoot) < best_score {
            best_score = undershoot + overshoot;
            best_paths = Vec::from([source_path.clone()]);
            best_file_set = candidate_tree.to_vec();
        }

        /*
         * This is the counterpart to the overshoot detection -- this is effectively
         * undershoot detection. When max_depth is 0 there can be one more directory
         * level found, 1 means 2 levels can be added, et cetera. This has a similar
         * issue as the overshoot detection characteristic where it's dependent on a
         * specific cost/score function. Depends on a decreasing cardinality sorting
         * of possible source directories. Because further directories searched will
         * all provide at most as much as the currently found directory even if they
         * are purely applicable hashes and don't overshoot at all they will at best
         * match the current score. <= is correct and tight, but if one wants to get
         * alternative matches, `<` can be used too.
         */
        if source_path_cards[source_path] * (max_depth + 1) <= undershoot {
            return (best_paths, best_score, best_file_set);
        }

        // Already found perfection, but wait until best match is updated.
        if undershoot == 0 && overshoot == 0 {
            return (best_paths, best_score, best_file_set);
        }

        // Too much overshoot, can't possibly become optimal through recursion
        // TODO mixes "score" and "raw count", which is okay-ish with and only
        // with COST_PER_DIRECTORY == 0
        if overshoot >= best_score {
            continue;
        }

        if max_depth > 0 {
            let next_accum_source_hashes = add_hash_bitmaps(candidate_tree, accum_source_hashes);
            let (candidate_paths, candidate_score, _) = brute_force_find_best_match(
                dest_hashes,
                source_path_cards,
                &next_accum_source_hashes,
                source_tree,
                // All permutations are equivalent, so only check a single
                // (arbitarily chosen) ordering.
                &possible_source_paths
                    .iter()
                    .skip(source_path_idx)
                    .filter(|p| !is_path_prefix(source_path, p))
                    .map(|e| e.clone())
                    .collect::<Vec<_>>(),
                max_depth - 1,
            );
            // Because each call of this function doesn't know about ancestor paths,
            // re-add it to get complete set.

            // TODO recreate the maybe_update_best_match template
            // @[sourcePath], undershoot + overshoot, candidateTree[])
            // Vec::from([source_path.clone()]) & candidate_paths, candidate_score +
            // COST_PER_DIRECTORY, next_accum_source_hashes)
            if (candidate_score + COST_PER_DIRECTORY) < best_score {
                best_score = candidate_score + COST_PER_DIRECTORY;
                best_paths = Vec::from([source_path.clone()]);
                best_paths.extend_from_slice(&candidate_paths);
                best_file_set = next_accum_source_hashes;
            }
        }
    }

    (best_paths, best_score, best_file_set)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let l0_lines = parse_file(&args[1]);
    let l1_lines = parse_file(&args[2]);
    let (common_hashes_seq, common_hashes) = get_common_hashes(&l0_lines, &l1_lines);

    let (l0_tree, l0_hash_index, l0_hash_index_files) =
        build_source_tree(&l0_lines, &common_hashes);
    let (l1_tree, _, l1_hash_index_files) = build_source_tree(&l1_lines, &common_hashes);
    let mut total_found_score: u32 = 0u32;
    let mut source_path_lens: HashMap<DirPath, u32> = HashMap::new();

    l0_tree.iter().for_each(|(dir_path, file_set)| {
        source_path_lens.insert(dir_path.clone(), card(file_set));
    });

    let now = Instant::now();
    l1_tree.iter().for_each(|(dir_path, file_set)| {
        let mut possible_source_paths =
            get_possible_source_paths(&l0_hash_index, &common_hashes_seq, file_set);

        // Help out the overshoot detector. As a general heuristic, checking larger
        // cardinality sets either achieves the desired outcome or overshoots, in a
        // quicker way. This doesn't matter that much in a single pass, but when an
        // additional pass is added, this can avoid many recursive calls altogether
        // resulting in a 3x to 4x measured speed increase exploiting commutativity
        // of sum in destHashes - (sourceHashes0 + sourceHashes1). It's safe, being
        // that it still checks all possibilities if it needs to.
        possible_source_paths.sort_by(|x, y| source_path_lens[y].cmp(&source_path_lens[x]));

        let (found_paths, found_score, found_file_set) = brute_force_find_best_match(
            file_set,
            &source_path_lens,
            &Vec::new(),
            &l0_tree,
            &possible_source_paths,
            1,
        );

        // TODO if child's closest match is a parent directory does that make sense?
        // not internally, at least, but across two file trees, maybe
        total_found_score += found_score;
        //if (found_paths.len() != 1 || &found_paths[0] != dir_path) && found_score > 0 {
        if found_paths.len() == 1 && found_score > 0 {
            // Special-case handling of empty foundFileSet here.
            // TODO treat this special case better
            //let added = sub_hash_bitmaps(file_set, &found_file_set);
            //let removed = sub_hash_bitmaps(&found_file_set, file_set);
            // TODO was template
            fn format_changed(x: FileSet) -> String {
                let mut s: String = "".to_string();
                for bit_index in get_set_bits(&x) {
                    //let y = common_hashes_seq[bitIndex];
                    const PREFIX: &str = "    ";
                    // TODO rewrite this formatting bit with a clear notion of indentation
                    // levels, etc, or just using JSON or something
                    // s &= prefix & $y & "\n"
                    // for z in l0_hash_indexFiles[y] {
                    //   s &= prefix & "  From: " & $z & "\n"
                    // }
                    // for z in l1HashIndexFiles[y] {
                    //  s &= prefix & "  To:   " & $z & "\n"
                    // }
                }
                s
            }
            println!(
                "{}: {} {}",
                format_dirpath(dir_path),
                format_dirpath(&found_paths[0]),
                found_score
            );
            //println!("{}: {}", format_dirpath(dir_path), found_score);
            //echo dirPath, ": ", foundPaths, " ", foundScore, "\n  Added:\n",
            //  formatChanged(added), "  Removed:\n", formatChanged(removed)
        }
    });

    println!("search time: {}", now.elapsed().as_secs());
    println!("TOTALFOUNDSCORE = {}", total_found_score);
}
