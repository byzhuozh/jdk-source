/*
 * Copyright (c) 1997, 2011, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package java.util;

/**
 * A Red-Black tree based {@link NavigableMap} implementation.
 * The map is sorted according to the {@linkplain Comparable natural
 * ordering} of its keys, or by a {@link Comparator} provided at map
 * creation time, depending on which constructor is used.
 * <p>
 * <p>This implementation provides guaranteed log(n) time cost for the
 * {@code containsKey}, {@code get}, {@code put} and {@code remove}
 * operations.  Algorithms are adaptations of those in Cormen, Leiserson, and
 * Rivest's <em>Introduction to Algorithms</em>.
 * <p>
 * <p>Note that the ordering maintained by a tree map, like any sorted map, and
 * whether or not an explicit comparator is provided, must be <em>consistent
 * with {@code equals}</em> if this sorted map is to correctly implement the
 * {@code Map} interface.  (See {@code Comparable} or {@code Comparator} for a
 * precise definition of <em>consistent with equals</em>.)  This is so because
 * the {@code Map} interface is defined in terms of the {@code equals}
 * operation, but a sorted map performs all key comparisons using its {@code
 * compareTo} (or {@code compare}) method, so two keys that are deemed equal by
 * this method are, from the standpoint of the sorted map, equal.  The behavior
 * of a sorted map <em>is</em> well-defined even if its ordering is
 * inconsistent with {@code equals}; it just fails to obey the general contract
 * of the {@code Map} interface.
 * <p>
 * <p><strong>Note that this implementation is not synchronized.</strong>
 * If multiple threads access a map concurrently, and at least one of the
 * threads modifies the map structurally, it <em>must</em> be synchronized
 * externally.  (A structural modification is any operation that adds or
 * deletes one or more mappings; merely changing the value associated
 * with an existing key is not a structural modification.)  This is
 * typically accomplished by synchronizing on some object that naturally
 * encapsulates the map.
 * If no such object exists, the map should be "wrapped" using the
 * {@link Collections#synchronizedSortedMap Collections.synchronizedSortedMap}
 * method.  This is best done at creation time, to prevent accidental
 * unsynchronized access to the map: <pre>
 *   SortedMap m = Collections.synchronizedSortedMap(new TreeMap(...));</pre>
 * <p>
 * <p>The iterators returned by the {@code iterator} method of the collections
 * returned by all of this class's "collection view methods" are
 * <em>fail-fast</em>: if the map is structurally modified at any time after
 * the iterator is created, in any way except through the iterator's own
 * {@code remove} method, the iterator will throw a {@link
 * ConcurrentModificationException}.  Thus, in the face of concurrent
 * modification, the iterator fails quickly and cleanly, rather than risking
 * arbitrary, non-deterministic behavior at an undetermined time in the future.
 * <p>
 * <p>Note that the fail-fast behavior of an iterator cannot be guaranteed
 * as it is, generally speaking, impossible to make any hard guarantees in the
 * presence of unsynchronized concurrent modification.  Fail-fast iterators
 * throw {@code ConcurrentModificationException} on a best-effort basis.
 * Therefore, it would be wrong to write a program that depended on this
 * exception for its correctness:   <em>the fail-fast behavior of iterators
 * should be used only to detect bugs.</em>
 * <p>
 * <p>All {@code Map.Entry} pairs returned by methods in this class
 * and its views represent snapshots of mappings at the time they were
 * produced. They do <strong>not</strong> support the {@code Entry.setValue}
 * method. (Note however that it is possible to change mappings in the
 * associated map using {@code put}.)
 * <p>
 * <p>This class is a member of the
 * <a href="{@docRoot}/../technotes/guides/collections/index.html">
 * Java Collections Framework</a>.
 *
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 * @author Josh Bloch and Doug Lea
 * @see Map
 * @see HashMap
 * @see Hashtable
 * @see Comparable
 * @see Comparator
 * @see Collection
 * @since 1.2
 */

public class TreeMap<K, V>
        extends AbstractMap<K, V>
        implements NavigableMap<K, V>, Cloneable, java.io.Serializable {
    /**
     * Dummy value serving as unmatchable fence key for unbounded
     * SubMapIterators
     */
    private static final Object UNBOUNDED = new Object();
    private static final boolean RED = false;
    private static final boolean BLACK = true;
    private static final long serialVersionUID = 919286545866124006L;
    /**
     * The comparator used to maintain order in this tree map, or
     * null if it uses the natural ordering of its keys.
     *
     * @serial 比较器
     */
    private final Comparator<? super K> comparator;
    // 红黑树根节点
    private transient Entry<K, V> root = null;
    /**
     * The number of entries in the tree
     * 集合元素数量
     */
    private transient int size = 0;
    /**
     * The number of structural modifications to the tree.
     * "fail-fast"集合修改记录
     */
    private transient int modCount = 0;


    // Query Operations
    /**
     * Fields initialized to contain an instance of the entry set view
     * the first time this view is requested.  Views are stateless, so
     * there's no reason to create more than one.
     */
    private transient EntrySet entrySet = null;
    private transient KeySet<K> navigableKeySet = null;
    private transient NavigableMap<K, V> descendingMap = null;

    /**
     * Constructs a new, empty tree map, using the natural ordering of its
     * keys.  All keys inserted into the map must implement the {@link
     * Comparable} interface.  Furthermore, all such keys must be
     * <em>mutually comparable</em>: {@code k1.compareTo(k2)} must not throw
     * a {@code ClassCastException} for any keys {@code k1} and
     * {@code k2} in the map.  If the user attempts to put a key into the
     * map that violates this constraint (for example, the user attempts to
     * put a string key into a map whose keys are integers), the
     * {@code put(Object key, Object value)} call will throw a
     * {@code ClassCastException}.
     *
     * 默认构造方法，comparator为空，代表使用key的自然顺序来维持TreeMap的顺序，这里要求key必须实现Comparable接口
     */
    public TreeMap() {
        comparator = null;
    }

    /**
     * Constructs a new, empty tree map, ordered according to the given
     * comparator.  All keys inserted into the map must be <em>mutually
     * comparable</em> by the given comparator: {@code comparator.compare(k1,
     * k2)} must not throw a {@code ClassCastException} for any keys
     * {@code k1} and {@code k2} in the map.  If the user attempts to put
     * a key into the map that violates this constraint, the {@code put(Object
     * key, Object value)} call will throw a
     * {@code ClassCastException}.
     *
     * @param comparator the comparator that will be used to order this map.
     *                   If {@code null}, the {@linkplain Comparable natural
     *                   ordering} of the keys will be used.
     *
     *  用指定的比较器构造一个TreeMap
     */
    public TreeMap(Comparator<? super K> comparator) {
        this.comparator = comparator;
    }

    /**
     * Constructs a new tree map containing the same mappings as the given
     * map, ordered according to the <em>natural ordering</em> of its keys.
     * All keys inserted into the new map must implement the {@link
     * Comparable} interface.  Furthermore, all such keys must be
     * <em>mutually comparable</em>: {@code k1.compareTo(k2)} must not throw
     * a {@code ClassCastException} for any keys {@code k1} and
     * {@code k2} in the map.  This method runs in n*log(n) time.
     *
     * @param m the map whose mappings are to be placed in this map
     * @throws ClassCastException   if the keys in m are not {@link Comparable},
     *                              or are not mutually comparable
     * @throws NullPointerException if the specified map is null
     *
     * 构造一个指定map的TreeMap，同样比较器comparator为空，使用key的自然顺序排序
     */
    public TreeMap(Map<? extends K, ? extends V> m) {
        comparator = null;
        putAll(m);
    }

    /**
     * Constructs a new tree map containing the same mappings and
     * using the same ordering as the specified sorted map.  This
     * method runs in linear time.
     *
     * @param m the sorted map whose mappings are to be placed in this map,
     *          and whose comparator is to be used to sort this map
     * @throws NullPointerException if the specified map is null
     *
     * 构造一个指定SortedMap的TreeMap，根据SortedMap的比较器来来维持TreeMap的顺序
     */
    public TreeMap(SortedMap<K, ? extends V> m) {
        comparator = m.comparator();
        try {
            buildFromSorted(m.size(), m.entrySet().iterator(), null, null);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }
    }

    /**
     * Test two values for equality.  Differs from o1.equals(o2) only in
     * that it copes with {@code null} o1 properly.
     */
    static final boolean valEquals(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }

    /**
     * Return SimpleImmutableEntry for entry, or null if null
     */
    static <K, V> Map.Entry<K, V> exportEntry(TreeMap.Entry<K, V> e) {
        return (e == null) ? null :
                new AbstractMap.SimpleImmutableEntry<>(e);
    }

    /**
     * Return key for entry, or null if null
     */
    static <K, V> K keyOrNull(TreeMap.Entry<K, V> e) {
        return (e == null) ? null : e.key;
    }

    /**
     * Returns the key corresponding to the specified Entry.
     *
     * @throws NoSuchElementException if the Entry is null
     */
    static <K> K key(Entry<K, ?> e) {
        if (e == null)
            throw new NoSuchElementException();
        return e.key;
    }

    /**
     * Returns the successor of the specified Entry, or null if no such.
     *
     * 查找要删除节点的替代节点
     */
    static <K, V> TreeMap.Entry<K, V> successor(Entry<K, V> t) {
        if (t == null)
            return null;
       // 查找右子树的最左孩子（左子树的最小节点）
        else if (t.right != null) {
            Entry<K, V> p = t.right;
            while (p.left != null)
                p = p.left;
            return p;
        } else {
            // 下面这段代码根本走不到，因为 deleteEntry 在调用此方法时传过来的 t 非 null
            // 查找左子树的最右孩子 -- 这部分表述是有问题的，不是往下找子节点的，而是往上找父节点的
            Entry<K, V> p = t.parent;
            Entry<K, V> ch = t;
            while (p != null && ch == p.right) {
                ch = p;
                p = p.parent;
            }
            return p;
        }
    }

    /**
     * Returns the predecessor of the specified Entry, or null if no such.
     */
    static <K, V> Entry<K, V> predecessor(Entry<K, V> t) {
        if (t == null)
            return null;
        else if (t.left != null) {
            Entry<K, V> p = t.left;
            while (p.right != null)
                p = p.right;
            return p;
        } else {
            Entry<K, V> p = t.parent;
            Entry<K, V> ch = t;
            while (p != null && ch == p.left) {
                ch = p;
                p = p.parent;
            }
            return p;
        }
    }

    /**
     * Balancing operations.
     * <p>
     * Implementations of rebalancings during insertion and deletion are
     * slightly different than the CLR version.  Rather than using dummy
     * nilnodes, we use a set of accessors that deal properly with null.  They
     * are used to avoid messiness surrounding nullness checks in the main
     * algorithms.
     */

    private static <K, V> boolean colorOf(Entry<K, V> p) {
        return (p == null ? BLACK : p.color);
    }

    private static <K, V> Entry<K, V> parentOf(Entry<K, V> p) {
        return (p == null ? null : p.parent);
    }

    private static <K, V> void setColor(Entry<K, V> p, boolean c) {
        if (p != null)
            p.color = c;
    }

    private static <K, V> Entry<K, V> leftOf(Entry<K, V> p) {
        return (p == null) ? null : p.left;
    }

    private static <K, V> Entry<K, V> rightOf(Entry<K, V> p) {
        return (p == null) ? null : p.right;
    }

    // NavigableMap API methods

    /**
     * Find the level down to which to assign all nodes BLACK.  This is the
     * last `full' level of the complete binary tree produced by
     * buildTree. The remaining nodes are colored RED. (This makes a `nice'
     * set of color assignments wrt future insertions.) This level number is
     * computed by finding the number of splits needed to reach the zeroeth
     * node.  (The answer is ~lg(N), but in any case must be computed by same
     * quick O(lg(N)) loop.)
     */
    private static int computeRedLevel(int sz) {
        int level = 0;
        for (int m = sz - 1; m >= 0; m = m / 2 - 1)
            level++;
        return level;
    }

    /**
     * Returns the number of key-value mappings in this map.
     *
     * @return the number of key-value mappings in this map
     */
    public int size() {
        return size;
    }

    /**
     * Returns {@code true} if this map contains a mapping for the specified
     * key.
     *
     * @param key key whose presence in this map is to be tested
     * @return {@code true} if this map contains a mapping for the
     * specified key
     * @throws ClassCastException   if the specified key cannot be compared
     *                              with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     */
    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }

    /**
     * Returns {@code true} if this map maps one or more keys to the
     * specified value.  More formally, returns {@code true} if and only if
     * this map contains at least one mapping to a value {@code v} such
     * that {@code (value==null ? v==null : value.equals(v))}.  This
     * operation will probably require time linear in the map size for
     * most implementations.
     *
     * @param value value whose presence in this map is to be tested
     * @return {@code true} if a mapping to {@code value} exists;
     * {@code false} otherwise
     * @since 1.2
     */
    public boolean containsValue(Object value) {
        for (Entry<K, V> e = getFirstEntry(); e != null; e = successor(e))
            if (valEquals(value, e.value))
                return true;
        return false;
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     * <p>
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code key} compares
     * equal to {@code k} according to the map's ordering, then this
     * method returns {@code v}; otherwise it returns {@code null}.
     * (There can be at most one such mapping.)
     * <p>
     * <p>A return value of {@code null} does not <em>necessarily</em>
     * indicate that the map contains no mapping for the key; it's also
     * possible that the map explicitly maps the key to {@code null}.
     * The {@link #containsKey containsKey} operation may be used to
     * distinguish these two cases.
     *
     * @throws ClassCastException   if the specified key cannot be compared
     *                              with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     */
    public V get(Object key) {
        Entry<K, V> p = getEntry(key);
        return (p == null ? null : p.value);
    }

    public Comparator<? super K> comparator() {
        return comparator;
    }

    /**
     * @throws NoSuchElementException {@inheritDoc}
     */
    public K firstKey() {
        return key(getFirstEntry());
    }

    /**
     * @throws NoSuchElementException {@inheritDoc}
     */
    public K lastKey() {
        return key(getLastEntry());
    }

    /**
     * Copies all of the mappings from the specified map to this map.
     * These mappings replace any mappings that this map had for any
     * of the keys currently in the specified map.
     *
     * @param map mappings to be stored in this map
     * @throws ClassCastException   if the class of a key or value in
     *                              the specified map prevents it from being stored in this map
     * @throws NullPointerException if the specified map is null or
     *                              the specified map contains a null key and this map does not
     *                              permit null keys
     */
    public void putAll(Map<? extends K, ? extends V> map) {
        int mapSize = map.size();
        if (size == 0 && mapSize != 0 && map instanceof SortedMap) {
            Comparator c = ((SortedMap) map).comparator();
            if (c == comparator || (c != null && c.equals(comparator))) {
                ++modCount;
                try {
                    buildFromSorted(mapSize, map.entrySet().iterator(),
                            null, null);
                } catch (java.io.IOException cannotHappen) {
                } catch (ClassNotFoundException cannotHappen) {
                }
                return;
            }
        }
        super.putAll(map);
    }

    /**
     * Returns this map's entry for the given key, or {@code null} if the map
     * does not contain an entry for the key.
     *
     * @return this map's entry for the given key, or {@code null} if the map
     * does not contain an entry for the key
     * @throws ClassCastException   if the specified key cannot be compared
     *                              with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     */
    final Entry<K, V> getEntry(Object key) {
        // Offload comparator-based version for sake of performance
        if (comparator != null)
            return getEntryUsingComparator(key);
        if (key == null)
            throw new NullPointerException();
        Comparable<? super K> k = (Comparable<? super K>) key;
        Entry<K, V> p = root;
        while (p != null) {
            int cmp = k.compareTo(p.key);
            if (cmp < 0)
                p = p.left;
            else if (cmp > 0)
                p = p.right;
            else
                return p;
        }
        return null;
    }

    /**
     * Version of getEntry using comparator. Split off from getEntry
     * for performance. (This is not worth doing for most methods,
     * that are less dependent on comparator performance, but is
     * worthwhile here.)
     */
    final Entry<K, V> getEntryUsingComparator(Object key) {
        K k = (K) key;
        Comparator<? super K> cpr = comparator;
        if (cpr != null) {
            Entry<K, V> p = root;
            while (p != null) {
                int cmp = cpr.compare(k, p.key);
                if (cmp < 0)
                    p = p.left;
                else if (cmp > 0)
                    p = p.right;
                else
                    return p;
            }
        }
        return null;
    }

    /**
     * Gets the entry corresponding to the specified key; if no such entry
     * exists, returns the entry for the least key greater than the specified
     * key; if no such entry exists (i.e., the greatest key in the Tree is less
     * than the specified key), returns {@code null}.
     */
    final Entry<K, V> getCeilingEntry(K key) {
        Entry<K, V> p = root;
        while (p != null) {
            int cmp = compare(key, p.key);
            if (cmp < 0) {
                if (p.left != null)
                    p = p.left;
                else
                    return p;
            } else if (cmp > 0) {
                if (p.right != null) {
                    p = p.right;
                } else {
                    Entry<K, V> parent = p.parent;
                    Entry<K, V> ch = p;
                    while (parent != null && ch == parent.right) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            } else
                return p;
        }
        return null;
    }

    // Views

    /**
     * Gets the entry corresponding to the specified key; if no such entry
     * exists, returns the entry for the greatest key less than the specified
     * key; if no such entry exists, returns {@code null}.
     */
    final Entry<K, V> getFloorEntry(K key) {
        Entry<K, V> p = root;
        while (p != null) {
            int cmp = compare(key, p.key);
            if (cmp > 0) {
                if (p.right != null)
                    p = p.right;
                else
                    return p;
            } else if (cmp < 0) {
                if (p.left != null) {
                    p = p.left;
                } else {
                    Entry<K, V> parent = p.parent;
                    Entry<K, V> ch = p;
                    while (parent != null && ch == parent.left) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            } else
                return p;

        }
        return null;
    }

    /**
     * Gets the entry for the least key greater than the specified
     * key; if no such entry exists, returns the entry for the least
     * key greater than the specified key; if no such entry exists
     * returns {@code null}.
     */
    final Entry<K, V> getHigherEntry(K key) {
        Entry<K, V> p = root;
        while (p != null) {
            int cmp = compare(key, p.key);
            if (cmp < 0) {
                if (p.left != null)
                    p = p.left;
                else
                    return p;
            } else {
                if (p.right != null) {
                    p = p.right;
                } else {
                    Entry<K, V> parent = p.parent;
                    Entry<K, V> ch = p;
                    while (parent != null && ch == parent.right) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            }
        }
        return null;
    }

    /**
     * Returns the entry for the greatest key less than the specified key; if
     * no such entry exists (i.e., the least key in the Tree is greater than
     * the specified key), returns {@code null}.
     */
    final Entry<K, V> getLowerEntry(K key) {
        Entry<K, V> p = root;
        while (p != null) {
            int cmp = compare(key, p.key);
            if (cmp > 0) {
                if (p.right != null)
                    p = p.right;
                else
                    return p;
            } else {
                if (p.left != null) {
                    p = p.left;
                } else {
                    Entry<K, V> parent = p.parent;
                    Entry<K, V> ch = p;
                    while (parent != null && ch == parent.left) {
                        ch = parent;
                        parent = parent.parent;
                    }
                    return parent;
                }
            }
        }
        return null;
    }

    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old
     * value is replaced.
     *
     * @param key   key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return the previous value associated with {@code key}, or
     * {@code null} if there was no mapping for {@code key}.
     * (A {@code null} return can also indicate that the map
     * previously associated {@code null} with {@code key}.)
     * @throws ClassCastException   if the specified key cannot be compared
     *                              with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     */
    public V put(K key, V value) {
        // 根节点
        Entry<K, V> t = root;
        // 如果根节点为空，则直接创建一个根节点，返回
        if (t == null) {
            compare(key, key); // type (and possibly null) check

            root = new Entry<>(key, value, null);  // 根节点默认黑色
            size = 1;
            modCount++;
            return null;
        }

        // 记录比较结果
        int cmp;
        Entry<K, V> parent;
        // split comparator and comparable paths
        // 当前使用的比较器
        Comparator<? super K> cpr = comparator;
        // 如果比较器不为空，就是用指定的比较器来维护TreeMap的元素顺序
        if (cpr != null) {
            // do while循环，查找key要插入的位置（也就是新节点的父节点是谁）
            do {
                // 记录上次循环的节点t
                parent = t;
                // 比较当前节点的key和新插入的key的大小
                cmp = cpr.compare(key, t.key);
                // 新插入的key小的话，则以当前节点的左孩子节点为新的比较节点
                if (cmp < 0)
                    t = t.left;
                // 新插入的key大的话，则以当前节点的右孩子节点为新的比较节点
                else if (cmp > 0)
                    t = t.right;
                else
                    // 如果当前节点的key和新插入的key相同的的话，则覆盖map的value，返回
                    return t.setValue(value);
             // 只有当t为null，也就是没有要比较节点的时候，代表已经找到新节点要插入的位置
            } while (t != null);
        } else {
            // 如果比较器为空，则使用key作为比较器进行比较
            // 这里要求key不能为空，并且必须实现Comparable接口
            if (key == null)
                throw new NullPointerException();
            // key 必须实现 Comparable 接口
            Comparable<? super K> k = (Comparable<? super K>) key;
            // 和上面一样，喜欢查找新节点要插入的位置
            do {
                parent = t;
                cmp = k.compareTo(t.key);
                if (cmp < 0)
                    t = t.left;
                else if (cmp > 0)
                    t = t.right;
                else
                    return t.setValue(value);
            } while (t != null);
        }
        // 找到新节点的父节点后，创建节点对象
        Entry<K, V> e = new Entry<>(key, value, parent);
        // 如果新节点key的值小于父节点key的值，则插在父节点的左侧
        if (cmp < 0)
            parent.left = e;
        else
            // 如果新节点key的值大于父节点key的值，则插在父节点的右侧
            parent.right = e;
        // 插入新的节点后，为了保持红黑树平衡，对红黑树进行调整
        fixAfterInsertion(e);
        // map元素个数+1
        size++;
        modCount++;
        return null;
    }

    /**
     * Removes the mapping for this key from this TreeMap if present.
     *
     * @param key key for which mapping should be removed
     * @return the previous value associated with {@code key}, or
     * {@code null} if there was no mapping for {@code key}.
     * (A {@code null} return can also indicate that the map
     * previously associated {@code null} with {@code key}.)
     * @throws ClassCastException   if the specified key cannot be compared
     *                              with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     */
    public V remove(Object key) {
        // 根据key查找到对应的节点对象
        Entry<K, V> p = getEntry(key);
        if (p == null)
            return null;

        // 记录key对应的value，供返回使用
        V oldValue = p.value;
        // 删除节点
        deleteEntry(p);
        return oldValue;
    }

    /**
     * Removes all of the mappings from this map.
     * The map will be empty after this call returns.
     */
    public void clear() {
        modCount++;
        size = 0;
        root = null;
    }

    /**
     * Returns a shallow copy of this {@code TreeMap} instance. (The keys and
     * values themselves are not cloned.)
     *
     * @return a shallow copy of this map
     */
    public Object clone() {
        TreeMap<K, V> clone = null;
        try {
            clone = (TreeMap<K, V>) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }

        // Put clone into "virgin" state (except for comparator)
        clone.root = null;
        clone.size = 0;
        clone.modCount = 0;
        clone.entrySet = null;
        clone.navigableKeySet = null;
        clone.descendingMap = null;

        // Initialize clone with our mappings
        try {
            clone.buildFromSorted(size, entrySet().iterator(), null, null);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }

        return clone;
    }

    /**
     * @since 1.6
     */
    public Map.Entry<K, V> firstEntry() {
        return exportEntry(getFirstEntry());
    }

    /**
     * @since 1.6
     */
    public Map.Entry<K, V> lastEntry() {
        return exportEntry(getLastEntry());
    }

    /**
     * @since 1.6
     */
    public Map.Entry<K, V> pollFirstEntry() {
        Entry<K, V> p = getFirstEntry();
        Map.Entry<K, V> result = exportEntry(p);
        if (p != null)
            deleteEntry(p);
        return result;
    }

    /**
     * @since 1.6
     */
    public Map.Entry<K, V> pollLastEntry() {
        Entry<K, V> p = getLastEntry();
        Map.Entry<K, V> result = exportEntry(p);
        if (p != null)
            deleteEntry(p);
        return result;
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public Map.Entry<K, V> lowerEntry(K key) {
        return exportEntry(getLowerEntry(key));
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public K lowerKey(K key) {
        return keyOrNull(getLowerEntry(key));
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public Map.Entry<K, V> floorEntry(K key) {
        return exportEntry(getFloorEntry(key));
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public K floorKey(K key) {
        return keyOrNull(getFloorEntry(key));
    }

    // View class support

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public Map.Entry<K, V> ceilingEntry(K key) {
        return exportEntry(getCeilingEntry(key));
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public K ceilingKey(K key) {
        return keyOrNull(getCeilingEntry(key));
    }

    /*
     * Unlike Values and EntrySet, the KeySet class is static,
     * delegating to a NavigableMap to allow use by SubMaps, which
     * outweighs the ugliness of needing type-tests for the following
     * Iterator methods that are defined appropriately in main versus
     * submap classes.
     */

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public Map.Entry<K, V> higherEntry(K key) {
        return exportEntry(getHigherEntry(key));
    }

    /**
     * @throws ClassCastException   {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     *                              and this map uses natural ordering, or its comparator
     *                              does not permit null keys
     * @since 1.6
     */
    public K higherKey(K key) {
        return keyOrNull(getHigherEntry(key));
    }

    /**
     * Returns a {@link Set} view of the keys contained in this map.
     * The set's iterator returns the keys in ascending order.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own {@code remove} operation), the results of
     * the iteration are undefined.  The set supports element removal,
     * which removes the corresponding mapping from the map, via the
     * {@code Iterator.remove}, {@code Set.remove},
     * {@code removeAll}, {@code retainAll}, and {@code clear}
     * operations.  It does not support the {@code add} or {@code addAll}
     * operations.
     */
    public Set<K> keySet() {
        return navigableKeySet();
    }

    /**
     * @since 1.6
     */
    public NavigableSet<K> navigableKeySet() {
        KeySet<K> nks = navigableKeySet;
        return (nks != null) ? nks : (navigableKeySet = new KeySet(this));
    }

    /**
     * @since 1.6
     */
    public NavigableSet<K> descendingKeySet() {
        return descendingMap().navigableKeySet();
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection's iterator returns the values in ascending order
     * of the corresponding keys.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  If the map is
     * modified while an iteration over the collection is in progress
     * (except through the iterator's own {@code remove} operation),
     * the results of the iteration are undefined.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the {@code Iterator.remove},
     * {@code Collection.remove}, {@code removeAll},
     * {@code retainAll} and {@code clear} operations.  It does not
     * support the {@code add} or {@code addAll} operations.
     */
    public Collection<V> values() {
        Collection<V> vs = values;
        return (vs != null) ? vs : (values = new Values());
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set's iterator returns the entries in ascending key order.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  If the map is modified
     * while an iteration over the set is in progress (except through
     * the iterator's own {@code remove} operation, or through the
     * {@code setValue} operation on a map entry returned by the
     * iterator) the results of the iteration are undefined.  The set
     * supports element removal, which removes the corresponding
     * mapping from the map, via the {@code Iterator.remove},
     * {@code Set.remove}, {@code removeAll}, {@code retainAll} and
     * {@code clear} operations.  It does not support the
     * {@code add} or {@code addAll} operations.
     */
    public Set<Map.Entry<K, V>> entrySet() {
        EntrySet es = entrySet;
        return (es != null) ? es : (entrySet = new EntrySet());
    }

    /**
     * @since 1.6
     */
    public NavigableMap<K, V> descendingMap() {
        NavigableMap<K, V> km = descendingMap;
        return (km != null) ? km :
                (descendingMap = new DescendingSubMap(this,
                        true, null, true,
                        true, null, true));
    }

    // Little utilities

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code fromKey} or {@code toKey} is
     *                                  null and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     * @since 1.6
     */
    public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive,
                                     K toKey, boolean toInclusive) {
        return new AscendingSubMap(this,
                false, fromKey, fromInclusive,
                false, toKey, toInclusive);
    }

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code toKey} is null
     *                                  and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     * @since 1.6
     */
    public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
        return new AscendingSubMap(this,
                true, null, true,
                false, toKey, inclusive);
    }

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code fromKey} is null
     *                                  and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     * @since 1.6
     */
    public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
        return new AscendingSubMap(this,
                false, fromKey, inclusive,
                true, null, true);
    }

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code fromKey} or {@code toKey} is
     *                                  null and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public SortedMap<K, V> subMap(K fromKey, K toKey) {
        return subMap(fromKey, true, toKey, false);
    }

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code toKey} is null
     *                                  and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public SortedMap<K, V> headMap(K toKey) {
        return headMap(toKey, false);
    }


    // SubMaps

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     if {@code fromKey} is null
     *                                  and this map uses natural ordering, or its comparator
     *                                  does not permit null keys
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public SortedMap<K, V> tailMap(K fromKey) {
        return tailMap(fromKey, true);
    }

    Iterator<K> keyIterator() {
        return new KeyIterator(getFirstEntry());
    }

    Iterator<K> descendingKeyIterator() {
        return new DescendingKeyIterator(getLastEntry());
    }

    /**
     * Compares two keys using the correct comparison method for this TreeMap.
     */
    final int compare(Object k1, Object k2) {
        return comparator == null ? ((Comparable<? super K>) k1).compareTo((K) k2)
                : comparator.compare((K) k1, (K) k2);
    }

    /**
     * Returns the first Entry in the TreeMap (according to the TreeMap's
     * key-sort function).  Returns null if the TreeMap is empty.
     */
    final Entry<K, V> getFirstEntry() {
        Entry<K, V> p = root;
        if (p != null)
            while (p.left != null)
                p = p.left;
        return p;
    }


    // Red-black mechanics

    /**
     * Returns the last Entry in the TreeMap (according to the TreeMap's
     * key-sort function).  Returns null if the TreeMap is empty.
     */
    final Entry<K, V> getLastEntry() {
        Entry<K, V> p = root;
        if (p != null)
            while (p.right != null)
                p = p.right;
        return p;
    }

    /**
     * 对红黑树的节点(x)进行左旋转
     *
     * 左旋示意图(对节点x进行左旋)：
     *      px                              px
     *     /                               /
     *    x                               y
     *   /  \      --(左旋)-->           / \
     *  lx   y                          x  ry
     *     /   \                       /  \
     *    ly   ry                     lx  ly
     *
     */
    private void rotateLeft(Entry<K, V> p) {
        if (p != null) {
            // 取得要选择节点p的右孩子
            Entry<K, V> r = p.right;
            // "p"和"r的左孩子"的相互指向...
            // 将"r的左孩子"设为"p的右孩子"
            p.right = r.left;
            // 如果r的左孩子非空，将"p"设为"r的左孩子的父亲"
            if (r.left != null)
                r.left.parent = p;

            // "p的父亲"和"r"的相互指向...
            // 将"p的父亲"设为"y的父亲"
            r.parent = p.parent;
            // 如果"p的父亲"是空节点，则将r设为根节点
            if (p.parent == null)
                root = r;
            // 如果p是它父节点的左孩子，则将r设为"p的父节点的左孩子"
            else if (p.parent.left == p)
                p.parent.left = r;
            else
                // 如果p是它父节点的左孩子，则将r设为"p的父节点的左孩子"
                p.parent.right = r;
            // "p"和"r"的相互指向...
            // 将"p"设为"r的左孩子"
            r.left = p;
            // 将"p的父节点"设为"r"
            p.parent = r;
        }
    }

    /**
     * 对红黑树的节点进行右旋转
     *
     * 右旋示意图(对节点y进行右旋)：
     *            py                               py
     *           /                                /
     *          y                                x
     *         /  \      --(右旋)--            /  \
     *        x   ry                           lx   y
     *       / \                                   / \
     *      lx  rx                                rx  ry
     *
     */
    private void rotateRight(Entry<K, V> p) {
        if (p != null) {
            // 取得要选择节点p的左孩子
            Entry<K, V> l = p.left;
            // 将"l的右孩子"设为"p的左孩子"
            p.left = l.right;
            // 如果"l的右孩子"不为空的话，将"p"设为"l的右孩子的父亲"
            if (l.right != null)
                l.right.parent = p;
            // 将"p的父亲"设为"l的父亲"
            l.parent = p.parent;
            // 如果"p的父亲"是空节点，则将l设为根节点
            if (p.parent == null)
                root = l;
            // 如果p是它父节点的右孩子，则将l设为"p的父节点的右孩子"
            else if (p.parent.right == p)
                p.parent.right = l;
            //如果p是它父节点的左孩子，将l设为"p的父节点的左孩子"
            else
                p.parent.left = l;
            // 将"p"设为"l的右孩子"
            l.right = p;
            // 将"l"设为"p父节点"
            p.parent = l;
        }
    }

    /**
     * From CLR
     *
     * 新增节点后对红黑树的调整方法
     */
    private void fixAfterInsertion(Entry<K, V> x) {
        // 将新插入节点的颜色设置为红色
        x.color = RED;
        // while循环，保证新插入节点x不是根节点或者新插入节点x的父节点不是红色（这两种情况不需要调整）
        while (x != null && x != root && x.parent.color == RED) {
            // 如果新插入节点x的父节点是爷爷节点的左孩子
            if (parentOf(x) == leftOf(parentOf(parentOf(x)))) {
                // 取得新插入节点x的叔叔节点
                Entry<K, V> y = rightOf(parentOf(parentOf(x)));
                // 如果新插入x的叔叔节点是红色-------------------①
                if (colorOf(y) == RED) {
                    // 将x的父节点设置为黑色
                    setColor(parentOf(x), BLACK);
                    // 将x的叔叔节点设置为黑色
                    setColor(y, BLACK);
                    // 将x的祖父节点设置为红色
                    setColor(parentOf(parentOf(x)), RED);
                    // 将x指向爷爷节点，如果x的爷爷节点的父节点是红色，按照上面的步奏继续循环
                    x = parentOf(parentOf(x));
                } else {
                    // 如果新插入x的叔叔节点是黑色或缺少，且x的父节点是祖父节点的右孩子-------------------②
                    if (x == rightOf(parentOf(x))) {
                        // 左旋父节点
                        x = parentOf(x);
                        rotateLeft(x);
                    }
                    // 如果新插入x的叔叔节点是黑色或缺少，且x的父节点是祖父节点的左孩子-------------------③
                    // 将x的父节点设置为黑色
                    setColor(parentOf(x), BLACK);
                    // 将x的祖父节点设置为红色
                    setColor(parentOf(parentOf(x)), RED);
                    // 右旋x的祖父节点
                    rotateRight(parentOf(parentOf(x)));
                }
            } else {  // 2. 如果新插入节点x的父节点是祖父节点的右孩子，下面的步奏和上面的相似，只不过左旋右旋的区分
                // 取祖父节点的左孩子节点
                Entry<K, V> y = leftOf(parentOf(parentOf(x)));
                //如果叔叔节点是红色，则直接着色即可
                if (colorOf(y) == RED) {
                    setColor(parentOf(x), BLACK);
                    setColor(y, BLACK);
                    setColor(parentOf(parentOf(x)), RED);
                    // 将x指向爷爷节点，如果x的爷爷节点的父节点是红色，按照上面的步奏继续循环
                    x = parentOf(parentOf(x));
                } else {
                    if (x == leftOf(parentOf(x))) {
                        // 右旋父节点
                        x = parentOf(x);
                        rotateRight(x);
                    }
                    // 将x的父节点设置为黑色
                    setColor(parentOf(x), BLACK);
                    //将x的祖父节点设置为红色
                    setColor(parentOf(parentOf(x)), RED);
                    //左旋转x的祖父节点 -- 即 爷爷节点
                    rotateLeft(parentOf(parentOf(x)));
                }
            }
        }
        // 最后将根节点设置为黑色，不管当前是不是红色，反正根节点必须是黑色
        root.color = BLACK;
    }

    /**
     * Delete node p, and then rebalance the tree.
     */
    private void deleteEntry(Entry<K, V> p) {
        modCount++;
        // map容器的元素个数减一
        size--;

        // If strictly internal, copy successor's element to p and then make p
        // point to successor.
        // 如果被删除的节点p的左孩子和右孩子都不为空，则查找其替代节点-----------这里表示要删除的节点有两个孩子（3）
        if (p.left != null && p.right != null) {
            // 查找p的替代节点
            Entry<K, V> s = successor(p);   // 该操作得到的肯定是p的右子树的最左节点！
            p.key = s.key;
            p.value = s.value;
            // 将p指向替代节点，之后的p不再是原先要删除的节点p，而是替代者p
            p = s;
        } // p has 2 children

        // Start fixup at replacement node, if it exists.
        // replacement为替代节点p的继承者，p的左孩子存在则用p的左孩子替代，否则用p的右孩子
        Entry<K, V> replacement = (p.left != null ? p.left : p.right);

        if (replacement != null) {   // 如果上面的if有两个孩子不通过--------------这里表示要删除的节点只有一个孩子
            // Link replacement to parent
            // 将p的父节点拷贝给替代节点
            replacement.parent = p.parent;

            // 如果替代节点p的父节点为空，也就是p为跟节点，则将replacement设置为根节点
            if (p.parent == null)
                root = replacement;

            // 如果替代节点p是其父节点的左孩子，则将replacement设置为其父节点的左孩子（子承父位）
            else if (p == p.parent.left)
                p.parent.left = replacement;

            // 如果替代节点p是其父节点的左孩子，则将replacement设置为其父节点的右孩子 （子承父位）
            else
                p.parent.right = replacement;

            // Null out links so they are OK to use by fixAfterDeletion.
            // 将替代节点p的left、right、parent的指针都指向空，即解除前后引用关系（相当于将p从树种摘除），使得gc可以回收
            p.left = p.right = p.parent = null;

            // Fix replacement
            // 如果替代节点p的颜色是黑色，则需要调整红黑树以保持其平衡
            if (p.color == BLACK)
                fixAfterDeletion(replacement);

        } else if (p.parent == null) { // return if we are the only node.
            // 如果要替代节点p没有父节点，代表p为根节点，直接删除即可
            root = null;

        } else { //  No children. Use self as phantom replacement and unlink.

            // 判断进入这里说明替代节点p没有孩子, p 自身是尾节点--------------这里表示没有孩子则直接删除（1）
            // 如果p的颜色是黑色，则调整红黑树
            if (p.color == BLACK)
                 fixAfterDeletion(p);

            // 下面删除替代节点p
            if (p.parent != null) {
                // 解除p的父节点对p的引用
                if (p == p.parent.left)
                    p.parent.left = null;
                else if (p == p.parent.right)
                    p.parent.right = null;
                // 解除p对p父节点的引用
                p.parent = null;
            }
        }
    }

    /**
     * From CLR
     */
    private void fixAfterDeletion(Entry<K, V> x) {
        // while循环，保证要删除节点x不是根节点，并且是黑色（根节点和红色不需要调整）
        while (x != root && colorOf(x) == BLACK) {

            // 如果要删除节点x是其父亲的左孩子
            if (x == leftOf(parentOf(x))) {

                // 取出要删除节点x的兄弟节点
                Entry<K, V> sib = rightOf(parentOf(x));

                // 如果删除节点x的兄弟节点是红色---------------------------①
                if (colorOf(sib) == RED) {
                    // 将x的兄弟节点颜色设置为黑色
                    setColor(sib, BLACK);
                    // 将x的父节点颜色设置为红色
                    setColor(parentOf(x), RED);
                    // 左旋x的父节点
                    rotateLeft(parentOf(x));
                    // 将sib重新指向旋转后x的兄弟节点 ，进入else的步奏③
                    sib = rightOf(parentOf(x));
                }

                // 如果x的兄弟节点的两个孩子都是黑色-------------------------③
                if (colorOf(leftOf(sib)) == BLACK &&
                        colorOf(rightOf(sib)) == BLACK) {
                    // 将兄弟节点的颜色设置为红色
                    setColor(sib, RED);
                    // 将x的父节点指向x，如果x的父节点是黑色，需要将x的父节点整天看做一个节点继续调整-------------------------②
                    x = parentOf(x);
                } else {
                    // 如果x的兄弟节点右孩子是黑色，左孩子是红色-------------------------④
                    if (colorOf(rightOf(sib)) == BLACK) {
                        // 将x的兄弟节点的左孩子设置为黑色
                        setColor(leftOf(sib), BLACK);
                        // 将x的兄弟节点设置为红色
                        setColor(sib, RED);
                        // 右旋x的兄弟节点
                        rotateRight(sib);
                        // 将sib重新指向旋转后x的兄弟节点，进入步奏⑤
                        sib = rightOf(parentOf(x));
                    }
                    // 如果x的兄弟节点右孩子是红色-------------------------⑤
                    setColor(sib, colorOf(parentOf(x)));
                    // 将x的父节点设置为黑色
                    setColor(parentOf(x), BLACK);
                    // 将x的兄弟节点的右孩子设置为黑色
                    setColor(rightOf(sib), BLACK);
                    // 左旋x的父节点
                    rotateLeft(parentOf(x));
                    // 达到平衡，将x指向root，退出循环
                    x = root;
                }
            } else { // symmetric
                // 如果要删除节点x是其父亲的右孩子，和上面情况一样
                Entry<K, V> sib = leftOf(parentOf(x));

                if (colorOf(sib) == RED) {
                    setColor(sib, BLACK);
                    setColor(parentOf(x), RED);
                    rotateRight(parentOf(x));
                    sib = leftOf(parentOf(x));
                }

                if (colorOf(rightOf(sib)) == BLACK &&
                        colorOf(leftOf(sib)) == BLACK) {
                    setColor(sib, RED);
                    x = parentOf(x);
                } else {
                    if (colorOf(leftOf(sib)) == BLACK) {
                        setColor(rightOf(sib), BLACK);
                        setColor(sib, RED);
                        rotateLeft(sib);
                        sib = leftOf(parentOf(x));
                    }
                    setColor(sib, colorOf(parentOf(x)));
                    setColor(parentOf(x), BLACK);
                    setColor(leftOf(sib), BLACK);
                    rotateRight(parentOf(x));
                    x = root;
                }
            }
        }

        setColor(x, BLACK);
    }

    /**
     * Save the state of the {@code TreeMap} instance to a stream (i.e.,
     * serialize it).
     *
     * @serialData The <em>size</em> of the TreeMap (the number of key-value
     * mappings) is emitted (int), followed by the key (Object)
     * and value (Object) for each key-value mapping represented
     * by the TreeMap. The key-value mappings are emitted in
     * key-order (as determined by the TreeMap's Comparator,
     * or by the keys' natural ordering if the TreeMap has no
     * Comparator).
     */
    private void writeObject(java.io.ObjectOutputStream s)
            throws java.io.IOException {
        // Write out the Comparator and any hidden stuff
        s.defaultWriteObject();

        // Write out size (number of Mappings)
        s.writeInt(size);

        // Write out keys and values (alternating)
        for (Iterator<Map.Entry<K, V>> i = entrySet().iterator(); i.hasNext(); ) {
            Map.Entry<K, V> e = i.next();
            s.writeObject(e.getKey());
            s.writeObject(e.getValue());
        }
    }

    /**
     * Reconstitute the {@code TreeMap} instance from a stream (i.e.,
     * deserialize it).
     */
    private void readObject(final java.io.ObjectInputStream s)
            throws java.io.IOException, ClassNotFoundException {
        // Read in the Comparator and any hidden stuff
        s.defaultReadObject();

        // Read in size
        int size = s.readInt();

        buildFromSorted(size, null, s, null);
    }

    /**
     * Intended to be called only from TreeSet.readObject
     */
    void readTreeSet(int size, java.io.ObjectInputStream s, V defaultVal)
            throws java.io.IOException, ClassNotFoundException {
        buildFromSorted(size, null, s, defaultVal);
    }

    /**
     * Intended to be called only from TreeSet.addAll
     */
    void addAllForTreeSet(SortedSet<? extends K> set, V defaultVal) {
        try {
            buildFromSorted(set.size(), set.iterator(), null, defaultVal);
        } catch (java.io.IOException cannotHappen) {
        } catch (ClassNotFoundException cannotHappen) {
        }
    }

    /**
     * Linear time tree building algorithm from sorted data.  Can accept keys
     * and/or values from iterator or stream. This leads to too many
     * parameters, but seems better than alternatives.  The four formats
     * that this method accepts are:
     * <p>
     * 1) An iterator of Map.Entries.  (it != null, defaultVal == null).
     * 2) An iterator of keys.         (it != null, defaultVal != null).
     * 3) A stream of alternating serialized keys and values.
     * (it == null, defaultVal == null).
     * 4) A stream of serialized keys. (it == null, defaultVal != null).
     * <p>
     * It is assumed that the comparator of the TreeMap is already set prior
     * to calling this method.
     *
     * @param size       the number of keys (or key-value pairs) to be read from
     *                   the iterator or stream
     * @param it         If non-null, new entries are created from entries
     *                   or keys read from this iterator.
     * @param str        If non-null, new entries are created from keys and
     *                   possibly values read from this stream in serialized form.
     *                   Exactly one of it and str should be non-null.
     * @param defaultVal if non-null, this default value is used for
     *                   each value in the map.  If null, each value is read from
     *                   iterator or stream, as described above.
     * @throws IOException            propagated from stream reads. This cannot
     *                                occur if str is null.
     * @throws ClassNotFoundException propagated from readObject.
     *                                This cannot occur if str is null.
     */
    private void buildFromSorted(int size, Iterator it,
                                 java.io.ObjectInputStream str,
                                 V defaultVal)
            throws java.io.IOException, ClassNotFoundException {
        this.size = size;
        root = buildFromSorted(0, 0, size - 1, computeRedLevel(size),
                it, str, defaultVal);
    }

    /**
     * Recursive "helper method" that does the real work of the
     * previous method.  Identically named parameters have
     * identical definitions.  Additional parameters are documented below.
     * It is assumed that the comparator and size fields of the TreeMap are
     * already set prior to calling this method.  (It ignores both fields.)
     *
     * @param level    the current level of tree. Initial call should be 0.
     * @param lo       the first element index of this subtree. Initial should be 0.
     * @param hi       the last element index of this subtree.  Initial should be
     *                 size-1.
     * @param redLevel the level at which nodes should be red.
     *                 Must be equal to computeRedLevel for tree of this size.
     */
    private final Entry<K, V> buildFromSorted(int level, int lo, int hi,
                                              int redLevel,
                                              Iterator it,
                                              java.io.ObjectInputStream str,
                                              V defaultVal)
            throws java.io.IOException, ClassNotFoundException {
        /*
         * Strategy: The root is the middlemost element. To get to it, we
         * have to first recursively construct the entire left subtree,
         * so as to grab all of its elements. We can then proceed with right
         * subtree.
         *
         * The lo and hi arguments are the minimum and maximum
         * indices to pull out of the iterator or stream for current subtree.
         * They are not actually indexed, we just proceed sequentially,
         * ensuring that items are extracted in corresponding order.
         */

        if (hi < lo) return null;

        int mid = (lo + hi) >>> 1;

        Entry<K, V> left = null;
        if (lo < mid)
            left = buildFromSorted(level + 1, lo, mid - 1, redLevel,
                    it, str, defaultVal);

        // extract key and/or value from iterator or stream
        K key;
        V value;
        if (it != null) {
            if (defaultVal == null) {
                Map.Entry<K, V> entry = (Map.Entry<K, V>) it.next();
                key = entry.getKey();
                value = entry.getValue();
            } else {
                key = (K) it.next();
                value = defaultVal;
            }
        } else { // use stream
            key = (K) str.readObject();
            value = (defaultVal != null ? defaultVal : (V) str.readObject());
        }

        Entry<K, V> middle = new Entry<>(key, value, null);

        // color nodes in non-full bottommost level red
        if (level == redLevel)
            middle.color = RED;

        if (left != null) {
            middle.left = left;
            left.parent = middle;
        }

        if (mid < hi) {
            Entry<K, V> right = buildFromSorted(level + 1, mid + 1, hi, redLevel,
                    it, str, defaultVal);
            middle.right = right;
            right.parent = middle;
        }

        return middle;
    }

    static final class KeySet<E> extends AbstractSet<E> implements NavigableSet<E> {
        private final NavigableMap<E, Object> m;

        KeySet(NavigableMap<E, Object> map) {
            m = map;
        }

        public Iterator<E> iterator() {
            if (m instanceof TreeMap)
                return ((TreeMap<E, Object>) m).keyIterator();
            else
                return (Iterator<E>) (((TreeMap.NavigableSubMap) m).keyIterator());
        }

        public Iterator<E> descendingIterator() {
            if (m instanceof TreeMap)
                return ((TreeMap<E, Object>) m).descendingKeyIterator();
            else
                return (Iterator<E>) (((TreeMap.NavigableSubMap) m).descendingKeyIterator());
        }

        public int size() {
            return m.size();
        }

        public boolean isEmpty() {
            return m.isEmpty();
        }

        public boolean contains(Object o) {
            return m.containsKey(o);
        }

        public void clear() {
            m.clear();
        }

        public E lower(E e) {
            return m.lowerKey(e);
        }

        public E floor(E e) {
            return m.floorKey(e);
        }

        public E ceiling(E e) {
            return m.ceilingKey(e);
        }

        public E higher(E e) {
            return m.higherKey(e);
        }

        public E first() {
            return m.firstKey();
        }

        public E last() {
            return m.lastKey();
        }

        public Comparator<? super E> comparator() {
            return m.comparator();
        }

        public E pollFirst() {
            Map.Entry<E, Object> e = m.pollFirstEntry();
            return (e == null) ? null : e.getKey();
        }

        public E pollLast() {
            Map.Entry<E, Object> e = m.pollLastEntry();
            return (e == null) ? null : e.getKey();
        }

        public boolean remove(Object o) {
            int oldSize = size();
            m.remove(o);
            return size() != oldSize;
        }

        public NavigableSet<E> subSet(E fromElement, boolean fromInclusive,
                                      E toElement, boolean toInclusive) {
            return new KeySet<>(m.subMap(fromElement, fromInclusive,
                    toElement, toInclusive));
        }

        public NavigableSet<E> headSet(E toElement, boolean inclusive) {
            return new KeySet<>(m.headMap(toElement, inclusive));
        }

        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
            return new KeySet<>(m.tailMap(fromElement, inclusive));
        }

        public SortedSet<E> subSet(E fromElement, E toElement) {
            return subSet(fromElement, true, toElement, false);
        }

        public SortedSet<E> headSet(E toElement) {
            return headSet(toElement, false);
        }

        public SortedSet<E> tailSet(E fromElement) {
            return tailSet(fromElement, true);
        }

        public NavigableSet<E> descendingSet() {
            return new KeySet(m.descendingMap());
        }
    }

    /**
     * @serial include
     */
    abstract static class NavigableSubMap<K, V> extends AbstractMap<K, V>
            implements NavigableMap<K, V>, java.io.Serializable {
        /**
         * The backing map.
         */
        final TreeMap<K, V> m;

        /**
         * Endpoints are represented as triples (fromStart, lo,
         * loInclusive) and (toEnd, hi, hiInclusive). If fromStart is
         * true, then the low (absolute) bound is the start of the
         * backing map, and the other values are ignored. Otherwise,
         * if loInclusive is true, lo is the inclusive bound, else lo
         * is the exclusive bound. Similarly for the upper bound.
         */
        final K lo, hi;
        final boolean fromStart, toEnd;
        final boolean loInclusive, hiInclusive;
        // Views
        transient NavigableMap<K, V> descendingMapView = null;

        // internal utilities
        transient EntrySetView entrySetView = null;
        transient KeySet<K> navigableKeySetView = null;

        NavigableSubMap(TreeMap<K, V> m,
                        boolean fromStart, K lo, boolean loInclusive,
                        boolean toEnd, K hi, boolean hiInclusive) {
            if (!fromStart && !toEnd) {
                if (m.compare(lo, hi) > 0)
                    throw new IllegalArgumentException("fromKey > toKey");
            } else {
                if (!fromStart) // type check
                    m.compare(lo, lo);
                if (!toEnd)
                    m.compare(hi, hi);
            }

            this.m = m;
            this.fromStart = fromStart;
            this.lo = lo;
            this.loInclusive = loInclusive;
            this.toEnd = toEnd;
            this.hi = hi;
            this.hiInclusive = hiInclusive;
        }

        final boolean tooLow(Object key) {
            if (!fromStart) {
                int c = m.compare(key, lo);
                if (c < 0 || (c == 0 && !loInclusive))
                    return true;
            }
            return false;
        }

        final boolean tooHigh(Object key) {
            if (!toEnd) {
                int c = m.compare(key, hi);
                if (c > 0 || (c == 0 && !hiInclusive))
                    return true;
            }
            return false;
        }

        /*
         * Absolute versions of relation operations.
         * Subclasses map to these using like-named "sub"
         * versions that invert senses for descending maps
         */

        final boolean inRange(Object key) {
            return !tooLow(key) && !tooHigh(key);
        }

        final boolean inClosedRange(Object key) {
            return (fromStart || m.compare(key, lo) >= 0)
                    && (toEnd || m.compare(hi, key) >= 0);
        }

        final boolean inRange(Object key, boolean inclusive) {
            return inclusive ? inRange(key) : inClosedRange(key);
        }

        final TreeMap.Entry<K, V> absLowest() {
            TreeMap.Entry<K, V> e =
                    (fromStart ? m.getFirstEntry() :
                            (loInclusive ? m.getCeilingEntry(lo) :
                                    m.getHigherEntry(lo)));
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absHighest() {
            TreeMap.Entry<K, V> e =
                    (toEnd ? m.getLastEntry() :
                            (hiInclusive ? m.getFloorEntry(hi) :
                                    m.getLowerEntry(hi)));
            return (e == null || tooLow(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absCeiling(K key) {
            if (tooLow(key))
                return absLowest();
            TreeMap.Entry<K, V> e = m.getCeilingEntry(key);
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absHigher(K key) {
            if (tooLow(key))
                return absLowest();
            TreeMap.Entry<K, V> e = m.getHigherEntry(key);
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absFloor(K key) {
            if (tooHigh(key))
                return absHighest();
            TreeMap.Entry<K, V> e = m.getFloorEntry(key);
            return (e == null || tooLow(e.key)) ? null : e;
        }

        // Abstract methods defined in ascending vs descending classes
        // These relay to the appropriate absolute versions

        final TreeMap.Entry<K, V> absLower(K key) {
            if (tooHigh(key))
                return absHighest();
            TreeMap.Entry<K, V> e = m.getLowerEntry(key);
            return (e == null || tooLow(e.key)) ? null : e;
        }

        /**
         * Returns the absolute high fence for ascending traversal
         */
        final TreeMap.Entry<K, V> absHighFence() {
            return (toEnd ? null : (hiInclusive ?
                    m.getHigherEntry(hi) :
                    m.getCeilingEntry(hi)));
        }

        /**
         * Return the absolute low fence for descending traversal
         */
        final TreeMap.Entry<K, V> absLowFence() {
            return (fromStart ? null : (loInclusive ?
                    m.getLowerEntry(lo) :
                    m.getFloorEntry(lo)));
        }

        abstract TreeMap.Entry<K, V> subLowest();

        abstract TreeMap.Entry<K, V> subHighest();

        abstract TreeMap.Entry<K, V> subCeiling(K key);

        abstract TreeMap.Entry<K, V> subHigher(K key);

        abstract TreeMap.Entry<K, V> subFloor(K key);

        // public methods

        abstract TreeMap.Entry<K, V> subLower(K key);

        /**
         * Returns ascending iterator from the perspective of this submap
         */
        abstract Iterator<K> keyIterator();

        /**
         * Returns descending iterator from the perspective of this submap
         */
        abstract Iterator<K> descendingKeyIterator();

        public boolean isEmpty() {
            return (fromStart && toEnd) ? m.isEmpty() : entrySet().isEmpty();
        }

        public int size() {
            return (fromStart && toEnd) ? m.size() : entrySet().size();
        }

        public final boolean containsKey(Object key) {
            return inRange(key) && m.containsKey(key);
        }

        public final V put(K key, V value) {
            if (!inRange(key))
                throw new IllegalArgumentException("key out of range");
            return m.put(key, value);
        }

        public final V get(Object key) {
            return !inRange(key) ? null : m.get(key);
        }

        public final V remove(Object key) {
            return !inRange(key) ? null : m.remove(key);
        }

        public final Map.Entry<K, V> ceilingEntry(K key) {
            return exportEntry(subCeiling(key));
        }

        public final K ceilingKey(K key) {
            return keyOrNull(subCeiling(key));
        }

        public final Map.Entry<K, V> higherEntry(K key) {
            return exportEntry(subHigher(key));
        }

        public final K higherKey(K key) {
            return keyOrNull(subHigher(key));
        }

        public final Map.Entry<K, V> floorEntry(K key) {
            return exportEntry(subFloor(key));
        }

        public final K floorKey(K key) {
            return keyOrNull(subFloor(key));
        }

        public final Map.Entry<K, V> lowerEntry(K key) {
            return exportEntry(subLower(key));
        }

        public final K lowerKey(K key) {
            return keyOrNull(subLower(key));
        }

        public final K firstKey() {
            return key(subLowest());
        }

        public final K lastKey() {
            return key(subHighest());
        }

        public final Map.Entry<K, V> firstEntry() {
            return exportEntry(subLowest());
        }

        public final Map.Entry<K, V> lastEntry() {
            return exportEntry(subHighest());
        }

        public final Map.Entry<K, V> pollFirstEntry() {
            TreeMap.Entry<K, V> e = subLowest();
            Map.Entry<K, V> result = exportEntry(e);
            if (e != null)
                m.deleteEntry(e);
            return result;
        }

        public final Map.Entry<K, V> pollLastEntry() {
            TreeMap.Entry<K, V> e = subHighest();
            Map.Entry<K, V> result = exportEntry(e);
            if (e != null)
                m.deleteEntry(e);
            return result;
        }

        public final NavigableSet<K> navigableKeySet() {
            KeySet<K> nksv = navigableKeySetView;
            return (nksv != null) ? nksv :
                    (navigableKeySetView = new TreeMap.KeySet(this));
        }

        public final Set<K> keySet() {
            return navigableKeySet();
        }

        public NavigableSet<K> descendingKeySet() {
            return descendingMap().navigableKeySet();
        }

        public final SortedMap<K, V> subMap(K fromKey, K toKey) {
            return subMap(fromKey, true, toKey, false);
        }

        public final SortedMap<K, V> headMap(K toKey) {
            return headMap(toKey, false);
        }

        public final SortedMap<K, V> tailMap(K fromKey) {
            return tailMap(fromKey, true);
        }

        // View classes

        abstract class EntrySetView extends AbstractSet<Map.Entry<K, V>> {
            private transient int size = -1, sizeModCount;

            public int size() {
                if (fromStart && toEnd)
                    return m.size();
                if (size == -1 || sizeModCount != m.modCount) {
                    sizeModCount = m.modCount;
                    size = 0;
                    Iterator i = iterator();
                    while (i.hasNext()) {
                        size++;
                        i.next();
                    }
                }
                return size;
            }

            public boolean isEmpty() {
                TreeMap.Entry<K, V> n = absLowest();
                return n == null || tooHigh(n.key);
            }

            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry))
                    return false;
                Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
                K key = entry.getKey();
                if (!inRange(key))
                    return false;
                TreeMap.Entry node = m.getEntry(key);
                return node != null &&
                        valEquals(node.getValue(), entry.getValue());
            }

            public boolean remove(Object o) {
                if (!(o instanceof Map.Entry))
                    return false;
                Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
                K key = entry.getKey();
                if (!inRange(key))
                    return false;
                TreeMap.Entry<K, V> node = m.getEntry(key);
                if (node != null && valEquals(node.getValue(),
                        entry.getValue())) {
                    m.deleteEntry(node);
                    return true;
                }
                return false;
            }
        }

        /**
         * Iterators for SubMaps
         */
        abstract class SubMapIterator<T> implements Iterator<T> {
            final Object fenceKey;
            TreeMap.Entry<K, V> lastReturned;
            TreeMap.Entry<K, V> next;
            int expectedModCount;

            SubMapIterator(TreeMap.Entry<K, V> first,
                           TreeMap.Entry<K, V> fence) {
                expectedModCount = m.modCount;
                lastReturned = null;
                next = first;
                fenceKey = fence == null ? UNBOUNDED : fence.key;
            }

            public final boolean hasNext() {
                return next != null && next.key != fenceKey;
            }

            final TreeMap.Entry<K, V> nextEntry() {
                TreeMap.Entry<K, V> e = next;
                if (e == null || e.key == fenceKey)
                    throw new NoSuchElementException();
                if (m.modCount != expectedModCount)
                    throw new ConcurrentModificationException();
                next = successor(e);
                lastReturned = e;
                return e;
            }

            final TreeMap.Entry<K, V> prevEntry() {
                TreeMap.Entry<K, V> e = next;
                if (e == null || e.key == fenceKey)
                    throw new NoSuchElementException();
                if (m.modCount != expectedModCount)
                    throw new ConcurrentModificationException();
                next = predecessor(e);
                lastReturned = e;
                return e;
            }

            final void removeAscending() {
                if (lastReturned == null)
                    throw new IllegalStateException();
                if (m.modCount != expectedModCount)
                    throw new ConcurrentModificationException();
                // deleted entries are replaced by their successors
                if (lastReturned.left != null && lastReturned.right != null)
                    next = lastReturned;
                m.deleteEntry(lastReturned);
                lastReturned = null;
                expectedModCount = m.modCount;
            }

            final void removeDescending() {
                if (lastReturned == null)
                    throw new IllegalStateException();
                if (m.modCount != expectedModCount)
                    throw new ConcurrentModificationException();
                m.deleteEntry(lastReturned);
                lastReturned = null;
                expectedModCount = m.modCount;
            }

        }

        final class SubMapEntryIterator extends SubMapIterator<Map.Entry<K, V>> {
            SubMapEntryIterator(TreeMap.Entry<K, V> first,
                                TreeMap.Entry<K, V> fence) {
                super(first, fence);
            }

            public Map.Entry<K, V> next() {
                return nextEntry();
            }

            public void remove() {
                removeAscending();
            }
        }

        final class SubMapKeyIterator extends SubMapIterator<K> {
            SubMapKeyIterator(TreeMap.Entry<K, V> first,
                              TreeMap.Entry<K, V> fence) {
                super(first, fence);
            }

            public K next() {
                return nextEntry().key;
            }

            public void remove() {
                removeAscending();
            }
        }

        final class DescendingSubMapEntryIterator extends SubMapIterator<Map.Entry<K, V>> {
            DescendingSubMapEntryIterator(TreeMap.Entry<K, V> last,
                                          TreeMap.Entry<K, V> fence) {
                super(last, fence);
            }

            public Map.Entry<K, V> next() {
                return prevEntry();
            }

            public void remove() {
                removeDescending();
            }
        }

        final class DescendingSubMapKeyIterator extends SubMapIterator<K> {
            DescendingSubMapKeyIterator(TreeMap.Entry<K, V> last,
                                        TreeMap.Entry<K, V> fence) {
                super(last, fence);
            }

            public K next() {
                return prevEntry().key;
            }

            public void remove() {
                removeDescending();
            }
        }
    }

    /**
     * @serial include
     */
    static final class AscendingSubMap<K, V> extends NavigableSubMap<K, V> {
        private static final long serialVersionUID = 912986545866124060L;

        AscendingSubMap(TreeMap<K, V> m,
                        boolean fromStart, K lo, boolean loInclusive,
                        boolean toEnd, K hi, boolean hiInclusive) {
            super(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive);
        }

        public Comparator<? super K> comparator() {
            return m.comparator();
        }

        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive,
                                         K toKey, boolean toInclusive) {
            if (!inRange(fromKey, fromInclusive))
                throw new IllegalArgumentException("fromKey out of range");
            if (!inRange(toKey, toInclusive))
                throw new IllegalArgumentException("toKey out of range");
            return new AscendingSubMap(m,
                    false, fromKey, fromInclusive,
                    false, toKey, toInclusive);
        }

        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
            if (!inRange(toKey, inclusive))
                throw new IllegalArgumentException("toKey out of range");
            return new AscendingSubMap(m,
                    fromStart, lo, loInclusive,
                    false, toKey, inclusive);
        }

        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
            if (!inRange(fromKey, inclusive))
                throw new IllegalArgumentException("fromKey out of range");
            return new AscendingSubMap(m,
                    false, fromKey, inclusive,
                    toEnd, hi, hiInclusive);
        }

        public NavigableMap<K, V> descendingMap() {
            NavigableMap<K, V> mv = descendingMapView;
            return (mv != null) ? mv :
                    (descendingMapView =
                            new DescendingSubMap(m,
                                    fromStart, lo, loInclusive,
                                    toEnd, hi, hiInclusive));
        }

        Iterator<K> keyIterator() {
            return new SubMapKeyIterator(absLowest(), absHighFence());
        }

        Iterator<K> descendingKeyIterator() {
            return new DescendingSubMapKeyIterator(absHighest(), absLowFence());
        }

        public Set<Map.Entry<K, V>> entrySet() {
            EntrySetView es = entrySetView;
            return (es != null) ? es : new AscendingEntrySetView();
        }

        TreeMap.Entry<K, V> subLowest() {
            return absLowest();
        }

        TreeMap.Entry<K, V> subHighest() {
            return absHighest();
        }

        TreeMap.Entry<K, V> subCeiling(K key) {
            return absCeiling(key);
        }

        TreeMap.Entry<K, V> subHigher(K key) {
            return absHigher(key);
        }

        TreeMap.Entry<K, V> subFloor(K key) {
            return absFloor(key);
        }

        TreeMap.Entry<K, V> subLower(K key) {
            return absLower(key);
        }

        final class AscendingEntrySetView extends EntrySetView {
            public Iterator<Map.Entry<K, V>> iterator() {
                return new SubMapEntryIterator(absLowest(), absHighFence());
            }
        }
    }

    /**
     * @serial include
     */
    static final class DescendingSubMap<K, V> extends NavigableSubMap<K, V> {
        private static final long serialVersionUID = 912986545866120460L;
        private final Comparator<? super K> reverseComparator =
                Collections.reverseOrder(m.comparator);

        DescendingSubMap(TreeMap<K, V> m,
                         boolean fromStart, K lo, boolean loInclusive,
                         boolean toEnd, K hi, boolean hiInclusive) {
            super(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive);
        }

        public Comparator<? super K> comparator() {
            return reverseComparator;
        }

        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive,
                                         K toKey, boolean toInclusive) {
            if (!inRange(fromKey, fromInclusive))
                throw new IllegalArgumentException("fromKey out of range");
            if (!inRange(toKey, toInclusive))
                throw new IllegalArgumentException("toKey out of range");
            return new DescendingSubMap(m,
                    false, toKey, toInclusive,
                    false, fromKey, fromInclusive);
        }

        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
            if (!inRange(toKey, inclusive))
                throw new IllegalArgumentException("toKey out of range");
            return new DescendingSubMap(m,
                    false, toKey, inclusive,
                    toEnd, hi, hiInclusive);
        }

        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
            if (!inRange(fromKey, inclusive))
                throw new IllegalArgumentException("fromKey out of range");
            return new DescendingSubMap(m,
                    fromStart, lo, loInclusive,
                    false, fromKey, inclusive);
        }

        public NavigableMap<K, V> descendingMap() {
            NavigableMap<K, V> mv = descendingMapView;
            return (mv != null) ? mv :
                    (descendingMapView =
                            new AscendingSubMap(m,
                                    fromStart, lo, loInclusive,
                                    toEnd, hi, hiInclusive));
        }

        Iterator<K> keyIterator() {
            return new DescendingSubMapKeyIterator(absHighest(), absLowFence());
        }

        Iterator<K> descendingKeyIterator() {
            return new SubMapKeyIterator(absLowest(), absHighFence());
        }

        public Set<Map.Entry<K, V>> entrySet() {
            EntrySetView es = entrySetView;
            return (es != null) ? es : new DescendingEntrySetView();
        }

        TreeMap.Entry<K, V> subLowest() {
            return absHighest();
        }

        TreeMap.Entry<K, V> subHighest() {
            return absLowest();
        }

        TreeMap.Entry<K, V> subCeiling(K key) {
            return absFloor(key);
        }

        TreeMap.Entry<K, V> subHigher(K key) {
            return absLower(key);
        }

        TreeMap.Entry<K, V> subFloor(K key) {
            return absCeiling(key);
        }

        TreeMap.Entry<K, V> subLower(K key) {
            return absHigher(key);
        }

        final class DescendingEntrySetView extends EntrySetView {
            public Iterator<Map.Entry<K, V>> iterator() {
                return new DescendingSubMapEntryIterator(absHighest(), absLowFence());
            }
        }
    }

    /**
     * Node in the Tree.  Doubles as a means to pass key-value pairs back to
     * user (see Map.Entry).
     */

    static final class Entry<K, V> implements Map.Entry<K, V> {
        K key;
        V value;
        // 左孩子节点
        Entry<K, V> left = null;
        // 右孩子节点
        Entry<K, V> right = null;
        // 父节点
        Entry<K, V> parent;
        // 红黑树用来表示节点颜色的属性，默认为黑色
        boolean color = BLACK;

        /**
         * Make a new cell with given key, value, and parent, and with
         * {@code null} child links, and BLACK color.
         * <p>
         * 用key，value和父节点构造一个Entry，默认为黑色
         */
        Entry(K key, V value, Entry<K, V> parent) {
            this.key = key;
            this.value = value;
            this.parent = parent;
        }

        /**
         * Returns the key.
         *
         * @return the key
         */
        public K getKey() {
            return key;
        }

        /**
         * Returns the value associated with the key.
         *
         * @return the value associated with the key
         */
        public V getValue() {
            return value;
        }

        /**
         * Replaces the value currently associated with the key with the given
         * value.
         *
         * @return the value associated with the key before this method was
         * called
         */
        public V setValue(V value) {
            V oldValue = this.value;
            this.value = value;
            return oldValue;
        }

        public boolean equals(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;

            return valEquals(key, e.getKey()) && valEquals(value, e.getValue());
        }

        public int hashCode() {
            int keyHash = (key == null ? 0 : key.hashCode());
            int valueHash = (value == null ? 0 : value.hashCode());
            return keyHash ^ valueHash;
        }

        public String toString() {
            return key + "=" + value;
        }
    }

    class Values extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return new ValueIterator(getFirstEntry());
        }

        public int size() {
            return TreeMap.this.size();
        }

        public boolean contains(Object o) {
            return TreeMap.this.containsValue(o);
        }

        public boolean remove(Object o) {
            for (Entry<K, V> e = getFirstEntry(); e != null; e = successor(e)) {
                if (valEquals(e.getValue(), o)) {
                    deleteEntry(e);
                    return true;
                }
            }
            return false;
        }

        public void clear() {
            TreeMap.this.clear();
        }
    }

    class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator(getFirstEntry());
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
            V value = entry.getValue();
            Entry<K, V> p = getEntry(entry.getKey());
            return p != null && valEquals(p.getValue(), value);
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<K, V> entry = (Map.Entry<K, V>) o;
            V value = entry.getValue();
            Entry<K, V> p = getEntry(entry.getKey());
            if (p != null && valEquals(p.getValue(), value)) {
                deleteEntry(p);
                return true;
            }
            return false;
        }

        public int size() {
            return TreeMap.this.size();
        }

        public void clear() {
            TreeMap.this.clear();
        }
    }

    /**
     * Base class for TreeMap Iterators
     */
    abstract class PrivateEntryIterator<T> implements Iterator<T> {
        Entry<K, V> next;
        Entry<K, V> lastReturned;
        int expectedModCount;

        PrivateEntryIterator(Entry<K, V> first) {
            expectedModCount = modCount;
            lastReturned = null;
            next = first;
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Entry<K, V> nextEntry() {
            Entry<K, V> e = next;
            if (e == null)
                throw new NoSuchElementException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            next = successor(e);
            lastReturned = e;
            return e;
        }

        final Entry<K, V> prevEntry() {
            Entry<K, V> e = next;
            if (e == null)
                throw new NoSuchElementException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            next = predecessor(e);
            lastReturned = e;
            return e;
        }

        public void remove() {
            if (lastReturned == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            // deleted entries are replaced by their successors
            if (lastReturned.left != null && lastReturned.right != null)
                next = lastReturned;
            deleteEntry(lastReturned);
            expectedModCount = modCount;
            lastReturned = null;
        }
    }

    final class EntryIterator extends PrivateEntryIterator<Map.Entry<K, V>> {
        EntryIterator(Entry<K, V> first) {
            super(first);
        }

        public Map.Entry<K, V> next() {
            return nextEntry();
        }
    }

    final class ValueIterator extends PrivateEntryIterator<V> {
        ValueIterator(Entry<K, V> first) {
            super(first);
        }

        public V next() {
            return nextEntry().value;
        }
    }

    final class KeyIterator extends PrivateEntryIterator<K> {
        KeyIterator(Entry<K, V> first) {
            super(first);
        }

        public K next() {
            return nextEntry().key;
        }
    }

    final class DescendingKeyIterator extends PrivateEntryIterator<K> {
        DescendingKeyIterator(Entry<K, V> first) {
            super(first);
        }

        public K next() {
            return prevEntry().key;
        }
    }

    /**
     * This class exists solely for the sake of serialization
     * compatibility with previous releases of TreeMap that did not
     * support NavigableMap.  It translates an old-version SubMap into
     * a new-version AscendingSubMap. This class is never otherwise
     * used.
     *
     * @serial include
     */
    private class SubMap extends AbstractMap<K, V>
            implements SortedMap<K, V>, java.io.Serializable {
        private static final long serialVersionUID = -6520786458950516097L;
        private boolean fromStart = false, toEnd = false;
        private K fromKey, toKey;

        private Object readResolve() {
            return new AscendingSubMap(TreeMap.this,
                    fromStart, fromKey, true,
                    toEnd, toKey, false);
        }

        public Set<Map.Entry<K, V>> entrySet() {
            throw new InternalError();
        }

        public K lastKey() {
            throw new InternalError();
        }

        public K firstKey() {
            throw new InternalError();
        }

        public SortedMap<K, V> subMap(K fromKey, K toKey) {
            throw new InternalError();
        }

        public SortedMap<K, V> headMap(K toKey) {
            throw new InternalError();
        }

        public SortedMap<K, V> tailMap(K fromKey) {
            throw new InternalError();
        }

        public Comparator<? super K> comparator() {
            throw new InternalError();
        }
    }
}
