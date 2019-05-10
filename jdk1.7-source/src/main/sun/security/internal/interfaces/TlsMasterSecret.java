/*
 * Copyright (c) 2005, 2010, Oracle and/or its affiliates. All rights reserved.
 * ORACLE PROPRIETARY/CONFIDENTIAL. Use is subject to license terms.
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 *
 */

package sun.security.internal.interfaces;

import javax.crypto.SecretKey;

/**
 * An SSL/TLS master secret key. It is a <code>SecretKey</code> that optionally
 * contains protocol version information that is used to detect version
 * rollback attacks during the SSL/TLS handshake.
 *
 * <p>Implementation of this interface are returned by the
 * <code>generateKey()</code> method of KeyGenerators of the type
 * "TlsMasterSecret".
 *
 * @since   1.6
 * @author  Andreas Sterbenz
 * @deprecated Sun JDK internal use only --- WILL BE REMOVED in a future
 * release.
 */
@Deprecated
public interface TlsMasterSecret extends SecretKey {

    public static final long serialVersionUID = -461748105810469773L;

    /**
     * Returns the major version number encapsulated in the premaster secret
     * this master secret was derived from, or -1 if it is not available.
     *
     * <p>This information will only usually only be available when RSA
     * was used as the key exchange algorithm.
     *
     * @return the major version number, or -1 if it is not available
     */
    public int getMajorVersion();

    /**
     * Returns the minor version number encapsulated in the premaster secret
     * this master secret was derived from, or -1 if it is not available.
     *
     * <p>This information will only usually only be available when RSA
     * was used as the key exchange algorithm.
     *
     * @return the major version number, or -1 if it is not available
     */
    public int getMinorVersion();

}
