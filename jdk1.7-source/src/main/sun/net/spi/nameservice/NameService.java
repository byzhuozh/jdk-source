/*
 * Copyright (c) 2000, 2005, Oracle and/or its affiliates. All rights reserved.
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

package sun.net.spi.nameservice;

import java.net.UnknownHostException;

public interface NameService {
    public java.net.InetAddress[] lookupAllHostAddr(String host) throws UnknownHostException;
    public String getHostByAddr(byte[] addr) throws UnknownHostException;
}
