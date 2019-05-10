/*
 * Copyright (c) 2000, Oracle and/or its affiliates. All rights reserved.
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

package sun.net.spi.nameservice.dns;

import sun.net.spi.nameservice.*;

public final class DNSNameServiceDescriptor implements NameServiceDescriptor {
    /**
     * Create a new instance of the corresponding name service.
     */
    public NameService createNameService() throws Exception {
        return new DNSNameService();
    }

    /**
     * Returns this service provider's name
     *
     */
    public String getProviderName() {
        return "sun";
    }

    /**
     * Returns this name service type
     * "dns" "nis" etc
     */
    public String getType() {
        return "dns";
    }
}
