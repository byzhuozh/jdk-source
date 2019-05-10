/*
 * Copyright (c) 1996, 2011, Oracle and/or its affiliates. All rights reserved.
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


package sun.security.ssl;


/**
 * SSL/TLS records, as pulled off (and put onto) a TCP stream.  This is
 * the base interface, which defines common information and interfaces
 * used by both Input and Output records.
 *
 * @author David Brownell
 */
interface Record {
    /*
     * There are four SSL record types, which are part of the interface
     * to this level (along with the maximum record size)
     *
     * enum { change_cipher_spec(20), alert(21), handshake(22),
     *      application_data(23), (255) } ContentType;
     */
    static final byte   ct_change_cipher_spec = 20;
    static final byte   ct_alert = 21;
    static final byte   ct_handshake = 22;
    static final byte   ct_application_data = 23;

    static final int    headerSize = 5;         // SSLv3 record header
    static final int    maxExpansion = 1024;    // for bad compression
    static final int    trailerSize = 20;       // SHA1 hash size
    static final int    maxDataSize = 16384;    // 2^14 bytes of data
    static final int    maxPadding = 256;       // block cipher padding
    static final int    maxIVLength = 256;      // block length

    /*
     * SSL has a maximum record size.  It's header, (compressed) data,
     * padding, and a trailer for the MAC.
     * Some compression algorithms have rare cases where they expand the data.
     * As we don't support compression at this time, leave that out.
     */
    static final int    maxRecordSize =
                                      headerSize        // header
                                    + maxIVLength       // iv
                                    + maxDataSize       // data
                                    + maxPadding        // padding
                                    + trailerSize;      // MAC

    static final boolean enableCBCProtection =
            Debug.getBooleanProperty("jsse.enableCBCProtection", true);

    /*
     * For CBC protection in SSL3/TLS1, we break some plaintext into two
     * packets.  Max application data size for the second packet.
     */
    static final int    maxDataSizeMinusOneByteRecord =
                                  maxDataSize       // max data size
                                - (                 // max one byte record size
                                      headerSize    // header
                                    + maxIVLength   // iv
                                    + 1             // one byte data
                                    + maxPadding    // padding
                                    + trailerSize   // MAC
                                  );

    /*
     * The maximum large record size.
     *
     * Some SSL/TLS implementations support large fragment upto 2^15 bytes,
     * such as Microsoft. We support large incoming fragments.
     *
     * The maximum large record size is defined as maxRecordSize plus 2^14,
     * this is the amount OpenSSL is using.
     */
    static final int    maxLargeRecordSize =
                maxRecordSize   // Max size with a conforming implemenation
              + maxDataSize;    // extra 2^14 bytes for large data packets.


    /*
     * Maximum record size for alert and change cipher spec records.
     * They only contain 2 and 1 bytes of data, respectively.
     * Allocate a smaller array.
     */
    static final int    maxAlertRecordSize =
                                      headerSize        // header
                                    + maxIVLength       // iv
                                    + 2                 // alert
                                    + maxPadding        // padding
                                    + trailerSize;      // MAC

}
