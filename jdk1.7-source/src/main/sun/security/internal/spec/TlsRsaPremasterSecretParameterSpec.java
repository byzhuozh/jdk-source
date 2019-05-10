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

package sun.security.internal.spec;

import java.security.spec.AlgorithmParameterSpec;

/**
 * Parameters for SSL/TLS RSA Premaster secret generation.
 * This class is used by SSL/TLS client to initialize KeyGenerators of the
 * type "TlsRsaPremasterSecret".
 *
 * <p>Instances of this class are immutable.
 *
 * @since   1.6
 * @author  Andreas Sterbenz
 * @deprecated Sun JDK internal use only --- WILL BE REMOVED in a future
 * release.
 */
@Deprecated
public class TlsRsaPremasterSecretParameterSpec
        implements AlgorithmParameterSpec {

    private final int majorVersion;
    private final int minorVersion;

    /**
     * Constructs a new TlsRsaPremasterSecretParameterSpec.
     *
     * <p>The version numbers will be placed inside the premaster secret to
     * detect version rollbacks attacks as described in the TLS specification.
     * Note that they do not indicate the protocol version negotiated for
     * the handshake.
     *
     * @param majorVersion the major number of the protocol version
     * @param minorVersion the minor number of the protocol version
     *
     * @throws IllegalArgumentException if minorVersion or majorVersion are
     *   negative or larger than 255
     */
    public TlsRsaPremasterSecretParameterSpec(int majorVersion,
            int minorVersion) {
        this.majorVersion =
            TlsMasterSecretParameterSpec.checkVersion(majorVersion);
        this.minorVersion =
            TlsMasterSecretParameterSpec.checkVersion(minorVersion); }

    /**
     * Returns the major version.
     *
     * @return the major version.
     */
    public int getMajorVersion() {
        return majorVersion;
    }

    /**
     * Returns the minor version.
     *
     * @return the minor version.
     */
    public int getMinorVersion() {
        return minorVersion;
    }
}
